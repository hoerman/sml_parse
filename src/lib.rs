#![allow(dead_code)]

mod sml_bin_parse;

use sml_bin_parse::SmlBinElement;
use sml_bin_parse::parse_into_binlist;

const SML_ESCAPE_SEQ: (u64, u64) = (0x1b1b1b1b_00000000,
                                    0xffffffff_00000000);
const SML_START_SEQ: u64 = 0x01010101;
const SML_ESCAPED_ESC_SEQ: (u64, u64) = (0x1b1b1b1b, 0xffffffff);
const SML_END_SEQ: (u64, u64) = (0x1a000000, 0xff000000);

#[derive(Debug, PartialEq)]
pub struct SmlBinFile {
    messages: Vec<SmlBinElement>,
}

pub struct SmlFile {
    messages: Vec<SmlMessage>,
}

pub struct SmlMessage {
    transaction_id: Vec<u8>,
    group_no: u8,
    abort_on_error: AbortOnError,
    message_body: SmlMessageBody,
    crc16: u16,
}

pub enum AbortOnError {
    Continue,
    SkipGroup,
    AbortAfterGrop,
    Abort,
}

pub enum SmlMessageBody {
    OpenRes(SmlOpenRes),
}

pub struct SmlOpenRes {
    codepage: Option<Vec<u8>>,
    client_id: Option<Vec<u8>>,
    req_file_id: Vec<u8>,
    server_id: Vec<u8>,
    ref_time: Option<SmlTime>,
    sml_version: Option<u8>,
}

pub enum SmlTime {
    SecIndex(u32),
    TimeStamp(u32),
    LocalTimeStamp { timestamp: u32,
                     local_offset: i16,
                     season_time_offset: i16 },
}        

#[derive(Debug, PartialEq)]
pub enum SmlError {
    NoError,
    UnexpectedEof,
    TLUnknownType,
    TLInvalidLen,
    TLInvalidPrimLen(usize),
    TLLenOutOfBounds,
    UnknownEscapeSequence,
    InvalidPaddingCnt,
}

pub type Result<T> = std::result::Result<T, SmlError>;

#[derive(Debug)]
struct SmlPreParse<'a, T: Iterator<Item=u8>> {
    data_iter: &'a mut T,
    escape_buf: u64,
    skip_esc_check: usize,
    iter_val: u8,
    error: SmlError,
    padding_bytes: usize,
    crc16_read: u16,
}

pub fn parse_iter_into_smlbinfile<'a, T>(i: &'a mut T)
    -> Result<Option<SmlBinFile>>
    where T: Iterator<Item=u8>
{
    let mut pre_parse = SmlPreParse::new(i);

    if !pre_parse.sml_search_start_escape() {
        return Ok(None);
    }

    let file_iter = pre_parse.build_file_iter()?;

    let binlist = parse_into_binlist(file_iter)?;

    Ok(Some(SmlBinFile { messages: binlist }))
}

impl<'a, T> SmlPreParse<'a, T>
    where T: Iterator<Item=u8>
{
    fn new(iter: &'a mut T) -> SmlPreParse<T>
    {
        SmlPreParse {
            data_iter: iter, escape_buf: 0, skip_esc_check: 0,
            iter_val: 0, error: SmlError::NoError,
            padding_bytes: 0, crc16_read: 0
        }
    }

    fn sml_search_start_escape(&mut self) -> bool
    {
        for c in &mut self.data_iter {
            self.escape_buf = self.escape_buf << 8 | c as u64;

            if self.escape_buf == SML_ESCAPE_SEQ.0 | SML_START_SEQ {
                return true;
            }
        }

        return false;
    }

    fn build_file_iter(&mut self) -> Result<&mut SmlPreParse<'a, T>>
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
mod tests_preparse {
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

#[cfg(test)]
mod tests_interface {
    use super::*;

    #[test]
    fn t_parse_empty()
    {
        let mut buf = vec![ ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(), None);
    }

    #[test]
    fn t_parse_garbage_only()
    {
        let mut buf = vec![ 0x01, 0x55, 0x03 ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(), None);
    }

    #[test]
    fn t_parse_complex()
    {
        let mut buf = vec![
            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* some garbage, shouldn't be consumed */
            0x55,
        ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));
        assert_eq!(buf.next(), Some(0x55));
    }

    fn build_complex_ref() -> Vec<SmlBinElement>
    {
        let mut base_list = Vec::new();
        base_list.push(SmlBinElement::OctetString(
                           [ 0x15, 0x17, 0x15, 0x56 ].to_vec())
                      );
        base_list.push(SmlBinElement::U8(0));
        base_list.push(SmlBinElement::U8(0));

        let mut inner1 = Vec::new();
        inner1.push(SmlBinElement::U16(0x0101));

        let mut inner11 = Vec::new();
        inner11.push(SmlBinElement::OctetString([].to_vec()));
        inner11.push(SmlBinElement::OctetString([].to_vec()));
        inner11.push(SmlBinElement::OctetString(
                         [ 0x17, 0x52, 0xac, 0xed ].to_vec())
                    );
        inner11.push(SmlBinElement::OctetString(
                         [ 0x0c, 0x31, 0x59, 0x54, 0x4d,
                           0x00, 0x13, 0xd1, 0xb0, 0x1f ].to_vec())
                    );
        inner11.push(SmlBinElement::OctetString([].to_vec()));
        inner11.push(SmlBinElement::OctetString([].to_vec()));

        inner1.push(SmlBinElement::List(inner11));
        base_list.push(SmlBinElement::List(inner1));

        base_list.push(SmlBinElement::U16(0xe80b));
        base_list.push(SmlBinElement::EndOfMsg);

        let mut res_list = Vec::new();
        res_list.push(SmlBinElement::List(base_list));

        res_list
    }

    #[test]
    fn t_parse_complex_double()
    {
        let mut buf = vec![
            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* some garbage, shouldn't be consumed */
            0x55,
        ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(buf.next(), Some(0x55));
    }

    #[test]
    fn t_parse_complex_double_garbage_deliminated()
    {
        let mut buf = vec![
            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* garbage to ignore */
            0x33, 0x66, 0x21, 0x33, 0x44,

            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* some garbage, shouldn't be consumed */
            0x55,
        ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(buf.next(), Some(0x55));
    }

    #[test]
    fn t_parse_complex_double_and_eom()
    {
        let mut buf = vec![
            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,
        ].into_iter();

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(), None);
    }

    #[test]
    fn t_parse_complex_escape_escape()
    {
        /* Todo: Is this size interpration correct? Does the TL header of the
         *       octet string describe the size of the decoded stream, i.e.
         *       without the four escape sequence bytes, or the size of the
         *       stream including the escape sequence bytes?
         */
        let mut buf = vec![
            /* start escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x01, 0x01, 0x01, 0x01,

            /* message */
            0x76,

            /* octet string 1b 1b 1b 1b (escaped with escape sequence) */
            0x05, 0x1b, 0x1b, 0x1b, 0x1b, 0x1b, 0x1b, 0x1b, 0x1b,

            0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00,

            /* eom escape */
            0x1b, 0x1b, 0x1b, 0x1b, 0x1a, 0x00, 0x00, 0x00,

            /* some garbage, shouldn't be consumed */
            0x55,
        ].into_iter();

        let mut ref_obj = build_complex_ref();
        match &mut ref_obj[0] {
            SmlBinElement::List(l) => match &mut l[0] {
                SmlBinElement::OctetString(ostr) => { ostr[0] = 0x1b;
                                                      ostr[1] = 0x1b;
                                                      ostr[2] = 0x1b;
                                                      ostr[3] = 0x1b },
                _ => panic!("ref obj doesn't match expectation (1)")
            }
            _ => panic!("ref obj doesn't match expectation (0)")
        }

        assert_eq!(parse_iter_into_smlbinfile(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: ref_obj }));
        assert_eq!(buf.next(), Some(0x55));
    }
}
