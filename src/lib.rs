#![allow(dead_code)]

const SML_ESCAPE_SEQ: (u64, u64) = (0x1b1b1b1b_00000000,
                                    0xffffffff_00000000);
const SML_START_SEQ: u64 = 0x01010101;
const SML_ESCAPED_ESC_SEQ: (u64, u64) = (0x1b1b1b1b, 0xffffffff);
const SML_END_SEQ: (u64, u64) = (0x1a000000, 0xff000000);

const TL_ENDOFMSG: (u8, u8) = (0x00, 0xff);
const TL_OCTET_STR: (u8, u8) = (0x00, 0x70);
const TL_BOOL: (u8, u8) = (0x40, 0x70);
const TL_INT: (u8, u8) = (0x50, 0x70);
const TL_UINT: (u8, u8) = (0x60, 0x70);
const TL_LIST: (u8, u8) = (0x70, 0x70);

pub struct SmlBinFile {
    messages: Vec<SmlBinElement>,
}

#[derive(Debug, PartialEq)]
pub enum SmlBinElement {
    OctetString(Vec<u8>),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Bool(bool),
    List(Vec<SmlBinElement>),
    EndOfMsg,
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
}

pub type Result<T> = std::result::Result<T, SmlError>;

struct SmlPreParse<'a, T: Iterator<Item=u8>> {
    data_iter: &'a mut T,
    escape_buf: u64,
    iter_val: u8,
    error: SmlError,
}

/* Tuple with decoded SML Type-Length-Field. The first element gives the
 * integer code of the data type, the second element gives the decoded
 * size.
 */
type SmlTL = (u8, usize);

pub fn parse_iter_into_smlbinfile<'a, T>(i: &'a mut T)
    -> Result<Option<SmlBinFile>>
    where T: Iterator<Item=u8>
{
    let mut pre_parse = SmlPreParse::new(i);

    if !pre_parse.sml_search_start_escape() {
        return Ok(None);
    }

    let file_iter = pre_parse.build_file_iter()?;

    let _binlist = parse_into_binlist(file_iter)?;

    Ok(None)
}

impl<'a, T> SmlPreParse<'a, T>
    where T: Iterator<Item=u8>
{
    fn new(iter: &'a mut T) -> SmlPreParse<T>
    {
        SmlPreParse { data_iter: iter, escape_buf: 0,
                      iter_val: 0, error: SmlError::NoError }
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
        if self.escape_buf & SML_ESCAPED_ESC_SEQ.1 == SML_ESCAPED_ESC_SEQ.1 {
            let iter_val = (SML_ESCAPED_ESC_SEQ.1 >> 24) as u8;

            match self.data_iter.next() {
                Some(val) => { self.escape_buf = self.escape_buf << 8 |
                               val as u64;
                               Some(iter_val) },
                None => { self.error = SmlError::UnexpectedEof; None }
            }
        } else if self.escape_buf & SML_END_SEQ.1 == SML_END_SEQ.0 {
            self.error = SmlError::NoError;

            None
        } else {
            self.error = SmlError::UnknownEscapeSequence;

            None
        }
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
        if self.escape_buf & SML_ESCAPE_SEQ.1 == SML_ESCAPE_SEQ.0 {
            self.escape_seq_read()
        } else {
            self.single_byte_read()
        }
    }

}

fn parse_into_binlist<T>(buf: T) -> Result<Vec<SmlBinElement>>
    where T: IntoIterator<Item=u8>
{
    let mut list = Vec::new();
    let i = &mut buf.into_iter();

    while let Some(el) = sml_try_msg_from_iter(i)? {
        list.push(el);
    }

    Ok(list)
}

fn sml_try_msg_from_iter<T>(i: &mut T)
    -> Result<Option<SmlBinElement>>
    where T: Iterator<Item=u8>
{
    match sml_tl_from_iter(i) {
        Ok(tl) => {
            match sml_bin_el_from_iter_with_tl(i, tl) {
                Ok(el) => Ok(Some(el)),
                Err(err) => Err(err),
            }
        },
        Err(SmlError::UnexpectedEof) => Ok(None),
        Err(err) => Err(err),
    }
}

fn sml_bin_el_from_iter_with_tl<T>(i: &mut T, tl: SmlTL)
    -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    match tl {
        (t, len) if t == TL_ENDOFMSG.0 && len == 0 =>
            Ok(SmlBinElement::EndOfMsg),
        (t, len) if t == TL_OCTET_STR.0 => parse_octet_str(i, len - 1),
        (t, len) if t == TL_INT.0 => parse_int(i, len - 1),
        (t, len) if t == TL_UINT.0 => parse_uint(i, len - 1),
        (t, len) if t == TL_BOOL.0 => parse_bool(i, len - 1),
        (t, len) if t == TL_LIST.0 => parse_list(i, len),
        (_, _) => Err(SmlError::TLUnknownType)
    }
}

fn sml_bin_el_from_iter<T>(i: &mut T) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    let tl = sml_tl_from_iter(i)?;

    sml_bin_el_from_iter_with_tl(i, tl)
}

fn sml_tl_from_iter<T>(i: &mut T) -> Result<SmlTL>
    where T: Iterator<Item=u8>
{
    let el = i.next().ok_or(SmlError::UnexpectedEof)?;

    parse_tl(el, i)
}

/* parse Type-Length-Field which describes the following message element.
 *
 * bit 0 - bit 3 encode the length of the following data
 *               for simple types this describes the data size in bytes
 *               including the tl field, for lists this describes the
 *               number of list elements, exlusive the tl field
 * bit 4 - bit 6 describes the type of the follwing data
 * bit 7         if set, the following byte encodes an continuation length
 *               field
 *
 * With each continuation length field the current size is shifted 4 bits
 * to the left and the size encoded in the lower 4 bits is added to the
 * result, giving the new length. If bit 7 is set an addition continuation
 * length field follows the current field. Bit 4 to 6 must be zero.
 */
fn parse_tl<T>(tl: u8, i: &mut T) -> Result<SmlTL>
    where T: Iterator<Item=u8>
{
    if tl & TL_ENDOFMSG.1 == TL_ENDOFMSG.0 {
        Ok((TL_ENDOFMSG.0, 0))
    } else if tl & TL_OCTET_STR.1 == TL_OCTET_STR.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            0 => Err(SmlError::TLInvalidLen),
            _ => Ok((TL_OCTET_STR.0, size)),
        }
    } else if tl & TL_BOOL.1 == TL_BOOL.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 => Ok((TL_BOOL.0, size)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_INT.1 == TL_INT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_INT.0, size)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_UINT.1 == TL_UINT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_UINT.0, size)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_LIST.1 == TL_LIST.0 {
        let size = parse_tl_len(tl, i)?;

        Ok((TL_LIST.0, size))
    } else {
        Err(SmlError::TLUnknownType)
    }
}

fn parse_tl_len<T>(tl: u8, i: &mut T) -> Result<usize>
    where T: Iterator<Item=u8>
{
    let size = tl as usize & 0x0f;

    if tl & 0x80 == 0x80 {
        parse_tl_len_cont(size, i, 4)
    } else {
        Ok(size)
    }
}

fn parse_tl_len_cont< T>(size: usize, i: &mut T,
                         size_bits: usize) -> Result<usize>
    where T: Iterator<Item=u8>
{
    let ld = i.next().ok_or(SmlError::UnexpectedEof)?;

    if ld & 0x70 != 0 {
        Err(SmlError::TLInvalidLen)
    } else if size_bits + 4 > 32 {
        Err(SmlError::TLLenOutOfBounds)
    } else {
        let new_size = (size << 4) | (ld as usize & 0x0f);

        if ld & 0x80 == 0x80 {
            parse_tl_len_cont(new_size, i, size_bits + 4)
        } else {
            Ok(new_size)
        }
    }
}

fn parse_octet_str<T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    let str: Vec<u8> = it.take(len).map(|v| v).collect();

    if str.len() == len {
        Ok(SmlBinElement::OctetString(str))
    } else {
        Err(SmlError::UnexpectedEof)
    }
}

fn parse_int<T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    let (val, cnt) = it.take(len)
                       .fold((0 as i64, 0),
                             |acc, val| (acc.0 << 8 | val as i64,
                                         acc.1 + 1));

    if cnt == len {
        match cnt {
            1 => Ok(SmlBinElement::I8(val as i8)),
            2 => Ok(SmlBinElement::I16(val as i16)),
            4 => Ok(SmlBinElement::I32(val as i32)),
            8 => Ok(SmlBinElement::I64(val as i64)),
            _ => Err(SmlError::TLInvalidPrimLen(len + 1))
        }
    } else {
        Err(SmlError::UnexpectedEof)
    }
}

fn parse_uint<T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    let (val, cnt) = it.take(len)
                       .fold((0 as u64, 0),
                             |acc, val| (acc.0 << 8 | val as u64,
                                         acc.1 + 1));

    if cnt == len {
        match cnt {
            1 => Ok(SmlBinElement::U8(val as u8)),
            2 => Ok(SmlBinElement::U16(val as u16)),
            4 => Ok(SmlBinElement::U32(val as u32)),
            8 => Ok(SmlBinElement::U64(val as u64)),
            _ => Err(SmlError::TLInvalidPrimLen(len + 1))
        }
    } else {
        Err(SmlError::UnexpectedEof)
    }
}

fn parse_bool<T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    if len == 1 {
        let val = it.next().ok_or(SmlError::UnexpectedEof)?;

        Ok(SmlBinElement::Bool(val > 0))
    } else {
        Err(SmlError::TLInvalidPrimLen(len + 1))
    }
}

fn parse_list<T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=u8>
{
    let mut list_elements = Vec::new();
    
    for _ in 0..len {
        list_elements.push(sml_bin_el_from_iter(it)?);
    }

    Ok(SmlBinElement::List(list_elements))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_tl_octet_str_simple() {
        assert_eq!(parse_tl(0x01, &mut vec![].into_iter()).unwrap(),
                   (TL_OCTET_STR.0, 1));
        assert_eq!(parse_tl(0x02, &mut vec![].into_iter()).unwrap(),
                   (TL_OCTET_STR.0, 2));
    }

    #[test]
    fn t_tl_octet_str_doesnt_consume() {
        let dont_touch = &mut vec![ 0x02 ].into_iter();
        assert_eq!(parse_tl(0x0f, dont_touch).unwrap(),
                   (TL_OCTET_STR.0, 15));
        assert_eq!(dont_touch.next(), Some(0x02));
    }

    #[test]
    fn t_tl_octet_str_cont_single() {
        let cont_iter = &mut vec![ 0x02, 0xff ].into_iter();
        assert_eq!(parse_tl(0x8f, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0xf2));
        assert_eq!(cont_iter.next(), Some(0xff));
    }

    #[test]
    fn t_tl_octet_str_cont_max() {
        let cont_iter = &mut vec![ 0x82, 0x83, 0x84, 0x85,
                                   0x86, 0x87, 0x08, 0x11 ].into_iter();
        assert_eq!(parse_tl(0x81, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0x1234_5678));
        assert_eq!(cont_iter.next(), Some(0x11));
    }

    #[test]
    fn t_tl_octet_str_strange_len() {
        let cont_iter = &mut vec![ 0x02, 0xff ].into_iter();
        assert_eq!(parse_tl(0x80, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0x02));
        assert_eq!(cont_iter.next(), Some(0xff));
    }

    #[test]
    fn t_tl_octet_str_wrong_len() {
        assert_eq!(parse_tl(0x81, &mut vec![ 0x81, 0x51 ].into_iter()),
                   Err(SmlError::TLInvalidLen));
    }

    #[test]
    fn t_tl_bool() {
        assert_eq!(parse_tl(0x42, &mut vec![].into_iter()).unwrap(),
                   (TL_BOOL.0, 2));
    }

    #[test]
    fn t_tl_bool_wrong_len() {
        assert_eq!(parse_tl(0x41, &mut vec![].into_iter()),
                   Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_tl(0x43, &mut vec![].into_iter()),
                   Err(SmlError::TLInvalidPrimLen(3)));
    }

    #[test]
    fn t_tl_bool_strange_len() {
        assert_eq!(parse_tl(0x80 | 0x40, &mut vec![ 0x02 ].into_iter()).unwrap(),
                   (TL_BOOL.0, 2));
        assert_eq!(parse_tl(0x80 | 0x40,
                            &mut vec![ 0x80, 0x02 ].into_iter()).unwrap(),
                   (TL_BOOL.0, 2));
    }

    #[test]
    fn t_tl_i8() {
        assert_eq!(parse_tl(0x52, &mut vec![].into_iter()).unwrap(),
                   (TL_INT.0, 2));
    }

    #[test]
    fn t_tl_i16() {
        assert_eq!(parse_tl(0x53, &mut vec![].into_iter()).unwrap(),
                   (TL_INT.0, 3));
    }

    #[test]
    fn t_tl_i32() {
        assert_eq!(parse_tl(0x55, &mut vec![].into_iter()).unwrap(),
                   (TL_INT.0, 5));
    }

    #[test]
    fn t_tl_i64() {
        assert_eq!(parse_tl(0x59, &mut vec![].into_iter()).unwrap(),
                   (TL_INT.0, 9));
    }

    #[test]
    fn t_tl_int_wrong_len() {
        for i in 0..15 {
            match i {
                2 | 3 | 5 | 9 => { },
                l =>  assert_eq!(parse_tl(0x50 | l, &mut vec![].into_iter()),
                                 Err(SmlError::TLInvalidPrimLen(l as usize)))
            }
        }
    }

    #[test]
    fn t_tl_u8() {
        assert_eq!(parse_tl(0x62, &mut vec![].into_iter()).unwrap(),
                   (TL_UINT.0, 2));
    }

    #[test]
    fn t_tl_u16() {
        assert_eq!(parse_tl(0x63, &mut vec![].into_iter()).unwrap(),
                   (TL_UINT.0, 3));
    }

    #[test]
    fn t_tl_u32() {
        assert_eq!(parse_tl(0x65, &mut vec![].into_iter()).unwrap(),
                   (TL_UINT.0, 5));
    }

    #[test]
    fn t_tl_u64() {
        assert_eq!(parse_tl(0x69, &mut vec![].into_iter()).unwrap(),
                   (TL_UINT.0, 9));
    }

    #[test]
    fn t_tl_uint_wrong_len() {
        for i in 0..15 {
            match i {
                2 | 3 | 5 | 9 => { },
                l =>  assert_eq!(parse_tl(0x60 | l, &mut vec![].into_iter()),
                                 Err(SmlError::TLInvalidPrimLen(l as usize)))
            }
        }
    }

    #[test]
    fn t_tl_list_simple() {
        assert_eq!(parse_tl(0x71, &mut vec![].into_iter()).unwrap(),
                   (TL_LIST.0, 1));
        assert_eq!(parse_tl(0x72, &mut vec![].into_iter()).unwrap(),
                   (TL_LIST.0, 2));
    }

    #[test]
    fn t_tl_list_empty() {
        assert_eq!(parse_tl(0x70, &mut vec![].into_iter()).unwrap(),
                   (TL_LIST.0, 0));
    }

    #[test]
    fn t_tl_list_long() {
        assert_eq!(parse_tl(0x80 | 0x7f,
                            &mut vec![0x8f, 0x8f, 0x8f, 0x8f,
                                      0x8f, 0x8f, 0x0e ].into_iter()).unwrap(),
                   (TL_LIST.0, 0xffff_fffe));
    }

    #[test]
    fn t_tl_test_oversized_len() {
        let cont_iter = &mut vec![ 0x82, 0x83, 0x84, 0x85,
                                   0x86, 0x87, 0x88, 0x01 ].into_iter();

        assert_eq!(parse_tl(0x81, cont_iter),
                   Err(SmlError::TLLenOutOfBounds));
    }

    #[test]
    fn t_parse_octet_str() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_octet_str(i, 8).unwrap(),
                   SmlBinElement::OctetString(
                       [ 0x01, 0x02, 0x03, 0x4,
                         0xaa, 0xbb, 0xcc, 0x10 ].to_vec()));
        assert_eq!(i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_octet_str_empty() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_octet_str(i, 0).unwrap(),
                   SmlBinElement::OctetString([ ].to_vec()));
        assert_eq!(i.next().unwrap(), 0x01);
    }

    #[test]
    fn t_parse_octet_str_short() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_octet_str(i, 10), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_int_i8() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_int(i, 1).unwrap(),
                   SmlBinElement::I8(0x01));
        assert_eq!(i.next().unwrap(), 0x02);
    }

    #[test]
    fn t_parse_int_i16() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_int(i, 2).unwrap(),
                   SmlBinElement::I16(0x0102));
        assert_eq!(i.next().unwrap(), 0x03);
    }

    #[test]
    fn t_parse_int_i32() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_int(i, 4).unwrap(),
                   SmlBinElement::I32(0x01020304));
        assert_eq!(i.next().unwrap(), 0x0aa);
    }

    #[test]
    fn t_parse_int_i64() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_int(i, 8).unwrap(),
                   SmlBinElement::I64(0x01020304_aabbcc10));
        assert_eq!(i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_int_invalid_len() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_int(i, 3), Err(SmlError::TLInvalidPrimLen(4)));
        assert_eq!(parse_int(i, 0), Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_int(i, 5), Err(SmlError::TLInvalidPrimLen(6)));
    }

    #[test]
    fn t_parse_int_short() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc ].into_iter();

        assert_eq!(parse_int(i, 8), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_uint_u8() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_uint(i, 1).unwrap(),
                   SmlBinElement::U8(0x01));
        assert_eq!(i.next().unwrap(), 0x02);
    }

    #[test]
    fn t_parse_uint_u16() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_uint(i, 2).unwrap(),
                   SmlBinElement::U16(0x0102));
        assert_eq!(i.next().unwrap(), 0x03);
    }

    #[test]
    fn t_parse_uint_u32() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_uint(i, 4).unwrap(),
                   SmlBinElement::U32(0x01020304));
        assert_eq!(i.next().unwrap(), 0x0aa);
    }

    #[test]
    fn t_parse_uint_u64() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_uint(i, 8).unwrap(),
                   SmlBinElement::U64(0x01020304_aabbcc10));
        assert_eq!(i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_uint_invalid_len() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_uint(i, 3), Err(SmlError::TLInvalidPrimLen(4)));
        assert_eq!(parse_uint(i, 0), Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_uint(i, 5), Err(SmlError::TLInvalidPrimLen(6)));
    }

    #[test]
    fn t_parse_uint_short() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc ].into_iter();

        assert_eq!(parse_uint(i, 8), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_bool() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x00,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_bool(i, 1).unwrap(), SmlBinElement::Bool(true));
        assert_eq!(i.next().unwrap(), 0x02);

        assert_eq!(parse_bool(i, 1).unwrap(), SmlBinElement::Bool(true));
        assert_eq!(parse_bool(i, 1).unwrap(), SmlBinElement::Bool(false));
    }

    #[test]
    fn t_parse_bool_large_true() {
        let i = &mut vec![ 0xf0 ].into_iter();

        assert_eq!(parse_bool(i, 1).unwrap(), SmlBinElement::Bool(true));
    }

    #[test]
    fn t_parse_bool_invalid_len() {
        let i = &mut vec![ 0x01, 0x02, 0x03, 0x4,
                           0xaa, 0xbb, 0xcc, 0x10, 0xff ].into_iter();

        assert_eq!(parse_bool(i, 2), Err(SmlError::TLInvalidPrimLen(3)));
        assert_eq!(parse_bool(i, 3), Err(SmlError::TLInvalidPrimLen(4)));
        assert_eq!(parse_bool(i, 0), Err(SmlError::TLInvalidPrimLen(1)));
    }

    #[test]
    fn t_parse_bool_short() {
        let i = &mut vec![].into_iter();

        assert_eq!(parse_bool(i, 1), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_list_simple() {
        let i = &mut vec![ 0x42, 0x01, 0xcc ].into_iter();

        let list = parse_list(i, 1);
        let mut ref_list = Vec::new();
        ref_list.push(SmlBinElement::Bool(true));
        assert_eq!(list, Ok(SmlBinElement::List(ref_list)));
        assert_eq!(i.next().unwrap(), 0xcc);
    }

    #[test]
    fn t_parse_list_multiple_elements() {
        let i = &mut vec![ 0x42, 0x00, 0x53, 0x01, 0x02 ].into_iter();

        let list = parse_list(i, 2);
        let mut ref_list = Vec::new();
        ref_list.push(SmlBinElement::Bool(false));
        ref_list.push(SmlBinElement::I16(0x0102));
        assert_eq!(list, Ok(SmlBinElement::List(ref_list)));
    }

    #[test]
    fn t_parse_list_empty() {
        let i = &mut vec![ 0x42, 0x01, 0xcc ].into_iter();

        let list = parse_list(i, 0);
        let ref_list = Vec::new();
        assert_eq!(list, Ok(SmlBinElement::List(ref_list)));
        assert_eq!(i.next().unwrap(), 0x42);
    }

    #[test]
    fn t_parse_list_nested_simple() {
        let i = &mut vec![ 0x71, 0x42, 0x08, 0x55 ].into_iter();

        let list = parse_list(i, 1);
        let mut ref_list = Vec::new();
        let mut inner = Vec::new();
        inner.push(SmlBinElement::Bool(true));
        ref_list.push(SmlBinElement::List(inner));
        assert_eq!(list, Ok(SmlBinElement::List(ref_list)));
        assert_eq!(i.next().unwrap(), 0x55);
    }

    #[test]
    fn t_parse_list_nested_complex() {
        let i = &mut vec![ 0x62, 0xaa,
                           0x72, 0x42, 0x08, 0x71, 0x52, 0x55,
                           0x04, 0x11, 0x22, 0x33 ].into_iter();

        let list = parse_list(i, 3);

        let mut ref_list = Vec::new();
        ref_list.push(SmlBinElement::U8(0xaa));

        let mut inner = Vec::new();
        inner.push(SmlBinElement::Bool(true));

        let mut inner2 = Vec::new();
        inner2.push(SmlBinElement::I8(0x55));
        inner.push(SmlBinElement::List(inner2));

        ref_list.push(SmlBinElement::List(inner));

        ref_list.push(SmlBinElement::OctetString([ 0x11, 0x22, 0x33 ].to_vec()));

        assert_eq!(list, Ok(SmlBinElement::List(ref_list)));
    }

    #[test]
    fn t_sml_bin_el_from_iter_octet_str()
    {
        let i = &mut vec![ 0x05, 0x01, 0x02, 0x30, 0x40, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::OctetString(vec![ 0x01, 0x02, 0x30, 0x40 ]));
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_sml_bin_el_from_iter_bool()
    {
        let i = &mut vec![ 0x42, 0x01, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i).unwrap(), SmlBinElement::Bool(true));
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_sml_bin_el_from_iter_int()
    {
        let i = &mut vec![ 0x52, 0x01, 0x53, 0x11, 0x22, 0x55, 0x7a, 0xbb, 0xcc,
                           0xdd, 0x59, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                           0x01, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i).unwrap(), SmlBinElement::I8(1));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(), SmlBinElement::I16(0x1122));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::I32(0x7abb_ccdd));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::I64(i64::MIN + 1));
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_sml_bin_el_from_iter_uint()
    {
        let i = &mut vec![ 0x62, 0x01, 0x63, 0x11, 0x22, 0x65, 0x7a, 0xbb, 0xcc,
                           0xdd, 0x69, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                           0x01, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i).unwrap(), SmlBinElement::U8(1));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(), SmlBinElement::U16(0x1122));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::U32(0x7abb_ccdd));
        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::U64(u64::MAX / 2 + 2));
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_sml_bin_el_from_iter_list()
    {
        let i = &mut vec![ 0x72, 0x42, 0x00, 0x53,
                           0x00, 0x01, 0x00 ].into_iter();

        let mut list = Vec::new();
        list.push(SmlBinElement::Bool(false));
        list.push(SmlBinElement::I16(1));

        assert_eq!(sml_bin_el_from_iter(i).unwrap(),
                   SmlBinElement::List(list));
        assert_eq!(i.next().unwrap(), 0x00);
    }

    #[test]
    fn t_sml_bin_el_from_iter_unknown_type()
    {
        let i = &mut vec![ 0x10, 0x00, 0x00, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i), Err(SmlError::TLUnknownType));
    }

    #[test]
    fn t_sml_bin_el_from_iter_unknown_type_in_list()
    {
        let i = &mut vec![ 0x72, 0x10, 0x42, 0x00, 0x00 ].into_iter();

        assert_eq!(sml_bin_el_from_iter(i), Err(SmlError::TLUnknownType));
    }

    #[test]
    fn t_parse_into_binlist() {
        let buf = vec![ 0x72, 0x42, 0x00, 0x53, 0x00, 0x01 ].into_iter();

        let mut list = Vec::new();
        list.push(SmlBinElement::Bool(false));
        list.push(SmlBinElement::I16(1));

        let mut msgs = Vec::new();
        msgs.push(SmlBinElement::List(list));

        assert_eq!(parse_into_binlist(buf).unwrap(), msgs);
    }

    #[test]
    fn t_parse_into_binlist_empty() {
        let buf = vec![ ].into_iter();

        assert_eq!(parse_into_binlist(buf).unwrap(), Vec::new());
    }

    #[test]
    fn t_parse_into_binlist_invalid_el() {
        let buf = vec![ 0x72, 0x42, 0x00, 0x53, 0x00,
                        0x01, 0x80 | 0x50, 0x50 ].into_iter();

        assert_eq!(parse_into_binlist(buf), Err(SmlError::TLInvalidLen));
    }

    #[test]
    fn t_parse_into_binlist_short() {
        let buf = vec![ 0x72, 0x42, 0x00, 0x53, 0x00, ].into_iter();

        assert_eq!(parse_into_binlist(buf), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_into_binlist_complex() {
        let buf = vec![
            0x76, 0x05, 0x15, 0x17, 0x15, 0x56, 0x62, 0x00, 0x62, 0x00,
            0x72, 0x63, 0x01, 0x01, 0x76, 0x01, 0x01, 0x05, 0x17, 0x52,
            0xac, 0xed, 0x0b, 0x0c, 0x31, 0x59, 0x54, 0x4d, 0x00, 0x13,
            0xd1, 0xb0, 0x1f, 0x01, 0x01, 0x63, 0xe8, 0x0b, 0x00 ].into_iter();

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

        assert_eq!(parse_into_binlist(buf).unwrap(), res_list);
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
}
