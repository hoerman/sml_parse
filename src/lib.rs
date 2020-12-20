#![allow(dead_code)]

const TL_OCTET_STR: (u8, u8) = (0x00, 0x70);
const TL_BOOL: (u8, u8) = (0x42, 0xff);
const TL_INT: (u8, u8) = (0x50, 0xf0);
const TL_UINT: (u8, u8) = (0x60, 0xf0);
const TL_LIST: (u8, u8) = (0x70, 0x70);

pub struct SmlBinFile {
    messages: Vec<SmlBinList>,
}

pub struct SmlBinList {
    list: Vec<SmlBinElement>
}

pub enum SmlBinElement {
    OctectSting(Vec<u8>),
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
    TLInvalidIntLen,
    TLLenOutOfBounds,
}

pub type Result<T> = std::result::Result<T, SmlError>;

/* Tuple with decoded SML Type-Length-Field. The first element gives the
 * integer code of the data type, the second element gives the decoded
 * size.
 */
type SmlTL = (u8, u32);

pub fn parse_buf_to_smlbinfile(buf: &[u8]) -> SmlBinFile
{
    //let mut _iter = buf.into_iter();

    let msgs = parse_into_binlist(buf);
    
    SmlBinFile { messages: msgs }
}

fn parse_into_binlist<'a, T>(buf: T) -> Vec<SmlBinList>
    where T: IntoIterator<Item=&'a u8>
{
    let _el = sml_type_from_iter(&mut buf.into_iter());

    Vec::new()
}

fn sml_type_from_iter<'a, T>(i: &mut T) -> Result<SmlBinElement>
    where T: Iterator<Item=&'a u8>
{
    let _tl: SmlTL = sml_tl_from_iter(i)?;

    Ok(SmlBinElement::EndOfMsg)
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
            _ => Ok((TL_OCTET_STR.0, size)),
        }
    } else if tl & TL_BOOL.1 == TL_BOOL.0 {
        /* type bool has fixed length field, we don't need to parse it */
        Ok((TL_BOOL.0, 2))
    } else if tl & TL_INT.1 == TL_INT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_INT.0, size)),
            _ => Err(SmlError::TLInvalidIntLen),
        }
    } else if tl & TL_UINT.1 == TL_UINT.0 {
        let size = parse_tl_len(tl, i)?;

        match size {
            2 | 3 | 5 | 9 => Ok((TL_UINT.0, size)),
            _ => Err(SmlError::TLInvalidIntLen),
        }
    } else if tl & TL_LIST.1 == TL_LIST.0 {
        let size = parse_tl_len(tl, i)?;

        Ok((TL_LIST.0, size))
    } else {
        Err(SmlError::TLUnknownType)
    }
}

fn parse_tl_len<'a, T>(tl: u8, i: &mut T) -> Result<u32>
    where T: Iterator<Item=&'a u8>
{
    let size: u32 = tl as u32 & 0x0f;

    if tl & 0x80 == 0x80 {
        parse_tl_len_cont(size, i, 4)
    } else {
        Ok(size)
    }
}

fn parse_tl_len_cont<'a, T>(size: u32, i: &mut T,
                            size_bits: usize) -> Result<u32>
    where T: Iterator<Item=&'a u8>
{
    let ld = i.next().ok_or(SmlError::UnexpectedEof)?;

    if ld & 0x70 != 0 {
        Err(SmlError::TLInvalidLen)
    } else if size_bits + 4 > 32 {
        Err(SmlError::TLLenOutOfBounds)
    } else {
        let new_size = (size << 4) | (*ld as u32 & 0x0f);

        if ld & 0x80 == 0x80 {
            parse_tl_len_cont(new_size, i, size_bits + 4)
        } else {
            Ok(new_size)
        }
    }
}

    
#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

}

#[test]
fn tl_octet_str_simple() {
    assert_eq!(parse_tl(0x01, &mut [].iter()).unwrap(),
               (TL_OCTET_STR.0, 1));
    assert_eq!(parse_tl(0x02, &mut [].iter()).unwrap(),
               (TL_OCTET_STR.0, 2));
}

#[test]
fn tl_octet_str_doesnt_consume() {
    let dont_touch = &mut [ 0x02 ].iter();
    assert_eq!(parse_tl(0x0f, dont_touch).unwrap(), (TL_OCTET_STR.0, 15));
    assert_eq!(dont_touch.next(), Some(&0x02));
}

#[test]
fn tl_octet_str_cont_single() {
    let cont_iter = &mut [ 0x02, 0xff ].iter();
    assert_eq!(parse_tl(0x8f, cont_iter).unwrap(),
               (TL_OCTET_STR.0, 0xf2));
    assert_eq!(cont_iter.next(), Some(&0xff));
}

#[test]
fn tl_octet_str_cont_max() {
    let cont_iter = &mut [ 0x82, 0x83, 0x84, 0x85,
                           0x86, 0x87, 0x08, 0x11 ].iter();
    assert_eq!(parse_tl(0x81, cont_iter).unwrap(),
               (TL_OCTET_STR.0, 0x1234_5678));
    assert_eq!(cont_iter.next(), Some(&0x11));
}

#[test]
fn tl_octet_str_strange_len() {
    let cont_iter = &mut [ 0x02, 0xff ].iter();
    assert_eq!(parse_tl(0x80, cont_iter).unwrap(),
               (TL_OCTET_STR.0, 0x02));
    assert_eq!(cont_iter.next(), Some(&0xff));
}

#[test]
fn tl_octet_str_wrong_len() {
    assert_eq!(parse_tl(0x00, &mut [].iter()), Err(SmlError::TLInvalidLen));
}

#[test]
fn tl_test_oversized_len() {
    let cont_iter = &mut [ 0x82, 0x83, 0x84, 0x85,
                           0x86, 0x87, 0x88, 0x01 ].iter();
    assert_eq!(parse_tl(0x81, cont_iter), Err(SmlError::TLLenOutOfBounds));
}
    
