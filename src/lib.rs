#![allow(dead_code)]

const TL_OCTET_STR: (u8, u8) = (0x00, 0x70);
const TL_BOOL: (u8, u8) = (0x40, 0x70);
const TL_INT: (u8, u8) = (0x50, 0x70);
const TL_UINT: (u8, u8) = (0x60, 0x70);
const TL_LIST: (u8, u8) = (0x70, 0x70);

pub struct SmlBinFile {
    messages: Vec<SmlBinList>,
}

#[derive(Debug, PartialEq)]
pub struct SmlBinList {
    list: Vec<SmlBinElement>
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
    List(SmlBinList),
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
    UnexpectedEof,
    TLUnknownType,
    TLInvalidLen,
    TLInvalidPrimLen(usize),
    TLLenOutOfBounds,
}

pub type Result<T> = std::result::Result<T, SmlError>;

/* Tuple with decoded SML Type-Length-Field. The first element gives the
 * integer code of the data type, the second element gives the decoded
 * size.
 */
type SmlTL = (u8, usize);

pub fn parse_buf_to_smlbinfile(buf: &[u8]) -> SmlBinFile
{
    let msgs = parse_into_binlist(buf);
    
    SmlBinFile { messages: msgs }
}

fn parse_into_binlist<'a, T>(buf: T) -> Vec<SmlBinList>
    where T: IntoIterator<Item=&'a u8>
{
    let _el = sml_bin_el_from_iter(&mut buf.into_iter());

    Vec::new()
}

fn sml_bin_el_from_iter<'a, T>(i: &mut T) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let tl = sml_tl_from_iter(i)?;

    match tl {
        (t, len) if t == TL_OCTET_STR.0 => parse_octet_str(i, len),
        (t, len) if t == TL_INT.0 => parse_int(i, len),
        (t, len) if t == TL_UINT.0 => parse_uint(i, len),
        (t, len) if t == TL_BOOL.0 => parse_bool(i, len),
        (t, len) if t == TL_LIST.0 => parse_list(i, len),
        (_, _) => Ok(SmlBinElement::EndOfMsg)
    }
}

fn sml_tl_from_iter<'a, T>(i: &mut T) -> Result<SmlTL>
    where T: Iterator<Item=&'a u8>
{
    let el = i.next().ok_or(SmlError::UnexpectedEof)?;

    parse_tl(*el, i)
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
fn parse_tl<'a, T>(tl: u8, i: &mut T) -> Result<SmlTL>
    where T: Iterator<Item=&'a u8>
{
    if tl & TL_OCTET_STR.1 == TL_OCTET_STR.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            0 => Err(SmlError::TLInvalidLen),
            _ => Ok((TL_OCTET_STR.0, size - 1)),
        }
    } else if tl & TL_BOOL.1 == TL_BOOL.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 => Ok((TL_BOOL.0, size - 1)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_INT.1 == TL_INT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_INT.0, size - 1)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_UINT.1 == TL_UINT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_UINT.0, size - 1)),
            l => Err(SmlError::TLInvalidPrimLen(l)),
        }
    } else if tl & TL_LIST.1 == TL_LIST.0 {
        let size = parse_tl_len(tl, i)?;

        Ok((TL_LIST.0, size))
    } else {
        Err(SmlError::TLUnknownType)
    }
}

fn parse_tl_len<'a, T>(tl: u8, i: &mut T) -> Result<usize>
    where T: Iterator<Item=&'a u8>
{
    let size = tl as usize & 0x0f;

    if tl & 0x80 == 0x80 {
        parse_tl_len_cont(size, i, 4)
    } else {
        Ok(size)
    }
}

fn parse_tl_len_cont<'a, T>(size: usize, i: &mut T,
                            size_bits: usize) -> Result<usize>
    where T: Iterator<Item=&'a u8>
{
    let ld = i.next().ok_or(SmlError::UnexpectedEof)?;

    if ld & 0x70 != 0 {
        Err(SmlError::TLInvalidLen)
    } else if size_bits + 4 > 32 {
        Err(SmlError::TLLenOutOfBounds)
    } else {
        let new_size = (size << 4) | (*ld as usize & 0x0f);

        if ld & 0x80 == 0x80 {
            parse_tl_len_cont(new_size, i, size_bits + 4)
        } else {
            Ok(new_size)
        }
    }
}

fn parse_octet_str<'a, T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let str: Vec<u8> = it.take(len).map(|v| *v).collect();

    if str.len() == len {
        Ok(SmlBinElement::OctetString(str))
    } else {
        Err(SmlError::UnexpectedEof)
    }
}

fn parse_int<'a, T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let (val, cnt) = it.take(len)
                       .fold((0 as i64, 0),
                             |acc, val| (acc.0 << 8 | *val as i64,
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

fn parse_uint<'a, T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let (val, cnt) = it.take(len)
                       .fold((0 as u64, 0),
                             |acc, val| (acc.0 << 8 | *val as u64,
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

fn parse_bool<'a, T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    if len == 1 {
        let val = it.next().ok_or(SmlError::UnexpectedEof)?;

        Ok(SmlBinElement::Bool(*val > 0))
    } else {
        Err(SmlError::TLInvalidPrimLen(len + 1))
    }
}

fn parse_list<'a, T>(it: &mut T, len: usize) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let mut list_elements = Vec::new();
    
    for _ in 0..len {
        list_elements.push(sml_bin_el_from_iter(it)?);
    }

    Ok(SmlBinElement::List(SmlBinList { list: list_elements }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_tl_octet_str_simple() {
        assert_eq!(parse_tl(0x01, &mut [].iter()).unwrap(),
                   (TL_OCTET_STR.0, 0));
        assert_eq!(parse_tl(0x02, &mut [].iter()).unwrap(),
                   (TL_OCTET_STR.0, 1));
    }

    #[test]
    fn t_tl_octet_str_doesnt_consume() {
        let dont_touch = &mut [ 0x02 ].iter();
        assert_eq!(parse_tl(0x0f, dont_touch).unwrap(),
                   (TL_OCTET_STR.0, 14));
        assert_eq!(dont_touch.next(), Some(&0x02));
    }

    #[test]
    fn t_tl_octet_str_cont_single() {
        let cont_iter = &mut [ 0x02, 0xff ].iter();
        assert_eq!(parse_tl(0x8f, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0xf1));
        assert_eq!(cont_iter.next(), Some(&0xff));
    }

    #[test]
    fn t_tl_octet_str_cont_max() {
        let cont_iter = &mut [ 0x82, 0x83, 0x84, 0x85,
                               0x86, 0x87, 0x08, 0x11 ].iter();
        assert_eq!(parse_tl(0x81, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0x1234_5677));
        assert_eq!(cont_iter.next(), Some(&0x11));
    }

    #[test]
    fn t_tl_octet_str_strange_len() {
        let cont_iter = &mut [ 0x02, 0xff ].iter();
        assert_eq!(parse_tl(0x80, cont_iter).unwrap(),
                   (TL_OCTET_STR.0, 0x01));
        assert_eq!(cont_iter.next(), Some(&0xff));
    }

    #[test]
    fn t_tl_octet_str_wrong_len() {
        assert_eq!(parse_tl(0x00, &mut [].iter()),
                   Err(SmlError::TLInvalidLen));
    }

    #[test]
    fn t_tl_bool() {
        assert_eq!(parse_tl(0x42, &mut [].iter()).unwrap(),
                   (TL_BOOL.0, 1));
    }

    #[test]
    fn t_tl_bool_wrong_len() {
        assert_eq!(parse_tl(0x41, &mut [].iter()),
                   Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_tl(0x43, &mut [].iter()),
                   Err(SmlError::TLInvalidPrimLen(3)));
    }

    #[test]
    fn t_tl_bool_strange_len() {
        assert_eq!(parse_tl(0x80 | 0x40, &mut [ 0x02 ].iter()).unwrap(),
                   (TL_BOOL.0, 1));
        assert_eq!(parse_tl(0x80 | 0x40,
                            &mut [ 0x80, 0x02 ].iter()).unwrap(),
                   (TL_BOOL.0, 1));
    }

    #[test]
    fn t_tl_i8() {
        assert_eq!(parse_tl(0x52, &mut [].iter()).unwrap(),
                   (TL_INT.0, 1));
    }

    #[test]
    fn t_tl_i16() {
        assert_eq!(parse_tl(0x53, &mut [].iter()).unwrap(),
                   (TL_INT.0, 2));
    }

    #[test]
    fn t_tl_i32() {
        assert_eq!(parse_tl(0x55, &mut [].iter()).unwrap(),
                   (TL_INT.0, 4));
    }

    #[test]
    fn t_tl_i64() {
        assert_eq!(parse_tl(0x59, &mut [].iter()).unwrap(),
                   (TL_INT.0, 8));
    }

    #[test]
    fn t_tl_int_wrong_len() {
        for i in 0..15 {
            match i {
                2 | 3 | 5 | 9 => { },
                l =>  assert_eq!(parse_tl(0x50 | l, &mut [].iter()),
                                 Err(SmlError::TLInvalidPrimLen(l as usize)))
            }
        }
    }

    #[test]
    fn t_tl_u8() {
        assert_eq!(parse_tl(0x62, &mut [].iter()).unwrap(),
                   (TL_UINT.0, 1));
    }

    #[test]
    fn t_tl_u16() {
        assert_eq!(parse_tl(0x63, &mut [].iter()).unwrap(),
                   (TL_UINT.0, 2));
    }

    #[test]
    fn t_tl_u32() {
        assert_eq!(parse_tl(0x65, &mut [].iter()).unwrap(),
                   (TL_UINT.0, 4));
    }

    #[test]
    fn t_tl_u64() {
        assert_eq!(parse_tl(0x69, &mut [].iter()).unwrap(),
                   (TL_UINT.0, 8));
    }

    #[test]
    fn t_tl_uint_wrong_len() {
        for i in 0..15 {
            match i {
                2 | 3 | 5 | 9 => { },
                l =>  assert_eq!(parse_tl(0x60 | l, &mut [].iter()),
                                 Err(SmlError::TLInvalidPrimLen(l as usize)))
            }
        }
    }

    #[test]
    fn t_tl_list_simple() {
        assert_eq!(parse_tl(0x71, &mut [].iter()).unwrap(),
                   (TL_LIST.0, 1));
        assert_eq!(parse_tl(0x72, &mut [].iter()).unwrap(),
                   (TL_LIST.0, 2));
    }

    #[test]
    fn t_tl_list_empty() {
        assert_eq!(parse_tl(0x70, &mut [].iter()).unwrap(),
                   (TL_LIST.0, 0));
    }

    #[test]
    fn t_tl_list_long() {
        assert_eq!(parse_tl(0x80 | 0x7f,
                            &mut [0x8f, 0x8f, 0x8f, 0x8f,
                                  0x8f, 0x8f, 0x0e ].iter()).unwrap(),
                   (TL_LIST.0, 0xffff_fffe));
    }

    #[test]
    fn t_tl_test_oversized_len() {
        let cont_iter = &mut [ 0x82, 0x83, 0x84, 0x85,
                               0x86, 0x87, 0x88, 0x01 ].iter();

        assert_eq!(parse_tl(0x81, cont_iter),
                   Err(SmlError::TLLenOutOfBounds));
    }

    #[test]
    fn t_parse_octet_str() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_octet_str(i, 8).unwrap(),
                   SmlBinElement::OctetString(
                       [ 0x01, 0x02, 0x03, 0x4,
                         0xaa, 0xbb, 0xcc, 0x10 ].to_vec()));
        assert_eq!(*i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_octet_str_empty() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_octet_str(i, 0).unwrap(),
                   SmlBinElement::OctetString([ ].to_vec()));
        assert_eq!(*i.next().unwrap(), 0x01);
    }

    #[test]
    fn t_parse_octet_str_short() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_octet_str(i, 10), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_int_i8() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_int(i, 1).unwrap(),
                   SmlBinElement::I8(0x01));
        assert_eq!(*i.next().unwrap(), 0x02);
    }

    #[test]
    fn t_parse_int_i16() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_int(i, 2).unwrap(),
                   SmlBinElement::I16(0x0102));
        assert_eq!(*i.next().unwrap(), 0x03);
    }

    #[test]
    fn t_parse_int_i32() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_int(i, 4).unwrap(),
                   SmlBinElement::I32(0x01020304));
        assert_eq!(*i.next().unwrap(), 0x0aa);
    }

    #[test]
    fn t_parse_int_i64() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_int(i, 8).unwrap(),
                   SmlBinElement::I64(0x01020304_aabbcc10));
        assert_eq!(*i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_int_invalid_len() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_int(i, 3), Err(SmlError::TLInvalidPrimLen(4)));
        assert_eq!(parse_int(i, 0), Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_int(i, 5), Err(SmlError::TLInvalidPrimLen(6)));
    }

    #[test]
    fn t_parse_int_short() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc ].iter();

        assert_eq!(parse_int(i, 8), Err(SmlError::UnexpectedEof));
    }

    #[test]
    fn t_parse_uint_u8() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_uint(i, 1).unwrap(),
                   SmlBinElement::U8(0x01));
        assert_eq!(*i.next().unwrap(), 0x02);
    }

    #[test]
    fn t_parse_uint_u16() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_uint(i, 2).unwrap(),
                   SmlBinElement::U16(0x0102));
        assert_eq!(*i.next().unwrap(), 0x03);
    }

    #[test]
    fn t_parse_uint_u32() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_uint(i, 4).unwrap(),
                   SmlBinElement::U32(0x01020304));
        assert_eq!(*i.next().unwrap(), 0x0aa);
    }

    #[test]
    fn t_parse_uint_u64() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_uint(i, 8).unwrap(),
                   SmlBinElement::U64(0x01020304_aabbcc10));
        assert_eq!(*i.next().unwrap(), 0xff);
    }

    #[test]
    fn t_parse_uint_invalid_len() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc, 0x10, 0xff ].iter();

        assert_eq!(parse_uint(i, 3), Err(SmlError::TLInvalidPrimLen(4)));
        assert_eq!(parse_uint(i, 0), Err(SmlError::TLInvalidPrimLen(1)));
        assert_eq!(parse_uint(i, 5), Err(SmlError::TLInvalidPrimLen(6)));
    }

    #[test]
    fn t_parse_uint_short() {
        let i = &mut [ 0x01, 0x02, 0x03, 0x4,
                       0xaa, 0xbb, 0xcc ].iter();

        assert_eq!(parse_uint(i, 8), Err(SmlError::UnexpectedEof));
    }
}
