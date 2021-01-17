use super::SmlError;
use super::Result;

const SML_ESCAPE_SEQ: (u64, u64) = (0x1b1b1b1b_00000000,
                                    0xffffffff_00000000);
const SML_START_SEQ: u64 = 0x01010101;
const SML_ESCAPED_ESC_SEQ: (u64, u64) = (0x1b1b1b1b, 0xffffffff);
const SML_END_SEQ: (u64, u64) = (0x1a000000, 0xff000000);

#[derive(Debug)]
pub struct SmlPreParse<'a, T: Iterator<Item=u8>> {
    data_iter: &'a mut T,
    escape_buf: u64,
    skip_esc_check: usize,
    iter_val: u8,
    error: SmlError,
    padding_bytes: usize,
    crc16_read: u16,
}

impl<'a, T> SmlPreParse<'a, T>
    where T: Iterator<Item=u8>
{
    pub fn new(iter: &'a mut T) -> SmlPreParse<T>
    {
        SmlPreParse {
            data_iter: iter, escape_buf: 0, skip_esc_check: 0,
            iter_val: 0, error: SmlError::NoError,
            padding_bytes: 0, crc16_read: 0
        }
    }

    pub fn sml_search_start_escape(&mut self) -> bool
    {
        for c in &mut self.data_iter {
            self.escape_buf = self.escape_buf << 8 | c as u64;

            if self.escape_buf == SML_ESCAPE_SEQ.0 | SML_START_SEQ {
                return true;
            }
        }

        return false;
    }

    pub fn build_file_iter(&mut self) -> Result<&mut SmlPreParse<'a, T>>
    {
        let buf = &mut self.escape_buf;

        let cnt = self.data_iter.take(8).fold(0 as usize, |acc, c| {
            *buf = *buf << 8 | c as u64;
            acc + 1
        });

        // the sml file must at least contain the enf of message escape sequence
        if cnt != 8 {
            return Err(SmlError::UnexpectedEof);
        }

        Ok(self)
    }

    fn escape_seq_read(&mut self) -> Option<u8>
    {
        if self.escape_buf & SML_ESCAPED_ESC_SEQ.1 == SML_ESCAPED_ESC_SEQ.0 {
            self.process_escaped_esc_seq()
        } else if self.escape_buf & SML_END_SEQ.1 == SML_END_SEQ.0 {
            self.process_eom_esc_seq()
        } else {
            self.error = SmlError::UnknownEscapeSequence;

            None
        }
    }

    fn process_escaped_esc_seq(&mut self) -> Option<u8>
    {
        let iter_val = (SML_ESCAPED_ESC_SEQ.0 >> 24) as u8;

        /* drop the four leading escape bytes and the first payload byte from
         * the buffer and try to fill it with the next five bytes from the
         * source iterator.
         */
        let buf = &mut self.escape_buf;
        let cnt = self.data_iter.take(5).fold(0 as usize, |acc, c| {
            *buf = *buf << 8 | c as u64;
            acc + 1
        });

        /* skip escape sequence checking for the next 3 bytes of the buffer,
         * since this are the remaining payload bytes. Without this reading
         * two adjacent escape sequences would fail.
         */
        self.skip_esc_check = 3;

        if cnt == 5 {
            Some(iter_val)
        } else {
            self.error = SmlError::UnexpectedEof;
            None
        }
    }

    fn process_eom_esc_seq(&mut self) -> Option<u8>
    {
        self.padding_bytes = ((self.escape_buf >> 16) & 0xff) as usize;
        self.crc16_read = (self.escape_buf & 0xffff) as u16;

        if self.padding_bytes <= 3 {
            let pad: Vec<u8> = self.data_iter
                                   .take(self.padding_bytes)
                                   .collect();

            if pad.len() == self.padding_bytes {
                self.error = SmlError::NoError;
            } else {
                self.error = SmlError::UnexpectedEof;
            }
        } else {
            self.error = SmlError::InvalidPaddingCnt;
        }

        None
    }

    fn single_byte_read(&mut self) -> Option<u8>
    {
        let iter_val = (self.escape_buf >> 56) as u8;

        match self.data_iter.next() {
            Some(val) => { self.escape_buf = self.escape_buf << 8 |
                           val as u64;
                           Some(iter_val) },
            None => { self.error = SmlError::UnexpectedEof; None }
        }
    }
}

impl<'a, T> Iterator for SmlPreParse<'a, T>
    where T: Iterator<Item=u8>
{
    type Item = u8;

    fn next(&mut self) -> Option<u8>
    {
        if self.skip_esc_check > 0 {
            self.skip_esc_check -= 1;

            self.single_byte_read()
        } else if self.escape_buf & SML_ESCAPE_SEQ.1 == SML_ESCAPE_SEQ.0 {
            self.escape_seq_read()
        } else {
            self.single_byte_read()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_smlpreparse_build()
    {
        let _preparse = SmlPreParse::new(&mut vec![].into_iter());

        assert!(true)
    }

    #[test]
    fn t_search_start_escape()
    {
        let mut i = vec![0x1b, 0x1b, 0x1b, 0x1b,
                         0x01, 0x01, 0x01, 0x01, 0x00].into_iter();

        let mut pp = SmlPreParse::new(&mut i);

        assert_eq!(pp.sml_search_start_escape(), true);
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_search_start_escape_no_start_escape()
    {
        let mut i = vec![0x1b, 0x1b, 0x1b, 0x1b,
                         0x01, 0x01, 0x01, 0x00].into_iter();

        let mut pp = SmlPreParse::new(&mut i);

        assert_eq!(pp.sml_search_start_escape(), false);
    }

    #[test]
    fn t_search_start_escape_leading_garbage()
    {
        let mut i = vec![0x1b, 0x1b, 0x1b, 0x1b,
                         0x01, 0x01, 0x01, 0x00,
                         0xff, 0x31, 0xa2, 0x55,
                         0x1b, 0x1b, 0x1b, 0x1b,
                         0x01, 0x01, 0x01, 0x01,
                         0x01, 0x02, 0x03, 0x04 ].into_iter();

        let mut pp = SmlPreParse::new(&mut i);

        assert_eq!(pp.sml_search_start_escape(), true);
        assert_eq!(i.next().unwrap(), 0x01);
        assert_eq!(i.next().unwrap(), 0x02);
        assert_eq!(i.next().unwrap(), 0x03);
        assert_eq!(i.next().unwrap(), 0x04);
    }

    #[test]
    fn t_build_file_iter()
    {
        let mut i = vec![0x00, 0x00, 0x00, 0x00,
                         0x00, 0x00, 0x00, 0x00 ].into_iter();
        let mut pp = SmlPreParse::new(&mut i);

        let _ = pp.build_file_iter().unwrap();

        assert!(true);
    }

    #[test]
    fn t_build_file_iter_fail_empty_vec()
    {
        let mut i = vec![ ].into_iter();
        let mut pp = SmlPreParse::new(&mut i);

        match pp.build_file_iter() {
            Err(err) => assert_eq!(err, SmlError::UnexpectedEof),
            _ => assert!(false),
        }
    }

    #[test]
    fn t_build_file_iter_fail_short_vec()
    {
        let mut i = vec![ 0x00, 0x00, 0x00, 0x00,
                          0x00, 0x00, 0x00 ].into_iter();
        let mut pp = SmlPreParse::new(&mut i);

        match pp.build_file_iter() {
            Err(err) => assert_eq!(err, SmlError::UnexpectedEof),
            _ => assert!(false),
        }
    }

    #[test]
    fn t_iterator_unescaped()
    {
        let mut it = vec![ 0x00, 0x01, 0x20, 0x03,
                           0x40, 0x05, 0x60, 0x07,
                           0x11, 0x22, 0x33, 0x44,
                           0x55, 0x66, 0x77, 0x88 ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), Some(0x01));
        assert_eq!(i.next(), Some(0x20));
        assert_eq!(i.next(), Some(0x03));
        assert_eq!(i.next(), Some(0x40));
        assert_eq!(i.next(), Some(0x05));
        assert_eq!(i.next(), Some(0x60));
        assert_eq!(i.next(), Some(0x07));
    }

    #[test]
    fn t_iterator_missing_eof()
    {
        let mut it = vec![ 0x00, 0x01, 0x20, 0x03,
                           0x40, 0x05, 0x60, 0x07,
                           0x11, 0x22, 0x33, 0x44,
                           0x55, 0x66, 0x77,  ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), Some(0x01));
        assert_eq!(i.next(), Some(0x20));
        assert_eq!(i.next(), Some(0x03));
        assert_eq!(i.next(), Some(0x40));
        assert_eq!(i.next(), Some(0x05));
        assert_eq!(i.next(), Some(0x60));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::UnexpectedEof);
    }

    #[test]
    fn t_iterator_escape_escape()
    {
        let mut it = vec![ 0x00, 0x01, 0x20, 0x03,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x11, 0x22, 0x33, 0x44,
                           0x55, 0x66, 0x77, 0x88,
                           0x99, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), Some(0x01));
        assert_eq!(i.next(), Some(0x20));
        assert_eq!(i.next(), Some(0x03));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x11));
    }

    #[test]
    fn t_iterator_double_escape_escape()
    {
        let mut it = vec![ 0x00, 0x01, 0x20, 0x03,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x11, 0x22, 0x33, 0x44,
                           0x55, 0x66, 0x77, 0x88,
                           0x99, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), Some(0x01));
        assert_eq!(i.next(), Some(0x20));
        assert_eq!(i.next(), Some(0x03));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x1b));
        assert_eq!(i.next(), Some(0x11));
    }

    #[test]
    fn t_iterator_escape_short()
    {
        let mut it = vec![ 0x00,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x11, 0x22, 0x33, 0x44, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::UnexpectedEof);
    }

    #[test]
    fn t_iterator_escape_eom()
    {
        let mut it = vec![ 0x00,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1a, 0x00, 0x12, 0x34, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::NoError);
        assert_eq!(pp.padding_bytes, 0);
        assert_eq!(pp.crc16_read, 0x1234);
    }

    #[test]
    fn t_iterator_escape_eom_padding()
    {
        let mut it = vec![ 0x00,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1a, 0x03, 0x12, 0x34,
                           0x00, 0x00, 0x00, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::NoError);
        assert_eq!(pp.padding_bytes, 3);
        assert_eq!(pp.crc16_read, 0x1234);
    }

    #[test]
    fn t_iterator_escape_eom_short_padding()
    {
        let mut it = vec![ 0x00,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1a, 0x03, 0x12, 0x34,
                           0x00, 0x00, ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::UnexpectedEof);
        assert_eq!(pp.padding_bytes, 3);
        assert_eq!(pp.crc16_read, 0x1234);
    }

    #[test]
    fn t_iterator_escape_eom_invalid_padding_cnt()
    {
        let mut it = vec![ 0x00,
                           0x1b, 0x1b, 0x1b, 0x1b,
                           0x1a, 0x04, 0x12, 0x34,
                           0x01, 0x02, 0x03, 0x04 ].into_iter();

        let mut pp = SmlPreParse::new(&mut it);
        let i = pp.build_file_iter().unwrap();

        assert_eq!(i.next(), Some(0x00));
        assert_eq!(i.next(), None);

        assert_eq!(pp.error, SmlError::InvalidPaddingCnt);
        assert_eq!(pp.padding_bytes, 4);
        assert_eq!(pp.crc16_read, 0x1234);
    }
}

