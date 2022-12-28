#![allow(dead_code)]

mod sml_bin_parse;
mod sml_transport_v1;
pub mod sml_message;
mod sml_unit;

use sml_bin_parse::SmlBinElement;
use sml_bin_parse::parse_into_binlist;
use sml_message::SmlMessage;

#[derive(Debug, PartialEq)]
pub struct SmlBinFile {
    messages: Vec<SmlBinElement>,
}

#[derive(Clone,Debug)]
pub struct SmlFile {
    pub messages: Vec<SmlMessage>,
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
    InvalidSmlMsgStructure,
    UnknownAbortOnErrorVal(u8),
    MissingSmlOpenMsg,
    MissingSmlCloseMsg,
    UnknownMsgId(u32),
    UnknownTimeFormat(u8),
}

impl SmlError {
    pub fn is_final(&self) -> bool {
        match self {
            SmlError::NoError |
            SmlError::TLUnknownType |
            SmlError::TLInvalidLen |
            SmlError::TLInvalidPrimLen(_) |
            SmlError::TLLenOutOfBounds |
            SmlError::UnknownEscapeSequence |
            SmlError::InvalidPaddingCnt |
            SmlError::InvalidSmlMsgStructure |
            SmlError::UnknownAbortOnErrorVal(_) |
            SmlError::MissingSmlOpenMsg |
            SmlError::MissingSmlCloseMsg |
            SmlError::UnknownMsgId(_) |
            SmlError::UnknownTimeFormat(_) =>
                false,

            SmlError::UnexpectedEof =>
                true
        }
    }
}

pub type Result<T> = std::result::Result<T, SmlError>;

pub fn parse_v1_bin<'a, T>(i: &'a mut T)
    -> Result<Option<SmlBinFile>>
    where T: Iterator<Item=u8>
{
    let mut pre_parse = sml_transport_v1::SmlPreParse::new(i);

    if !pre_parse.sml_search_start_escape() {
        return Ok(None);
    }

    let file_iter = pre_parse.build_file_iter()?;

    let binlist = parse_into_binlist(file_iter)?;

    Ok(Some(SmlBinFile { messages: binlist }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_parse_empty()
    {
        let mut buf = vec![ ].into_iter();

        assert_eq!(parse_v1_bin(&mut buf).unwrap(), None);
    }

    #[test]
    fn t_parse_garbage_only()
    {
        let mut buf = vec![ 0x01, 0x55, 0x03 ].into_iter();

        assert_eq!(parse_v1_bin(&mut buf).unwrap(), None);
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

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
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

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
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

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
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

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: build_complex_ref() }));

        assert_eq!(parse_v1_bin(&mut buf).unwrap(), None);
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

        assert_eq!(parse_v1_bin(&mut buf).unwrap(),
                   Some(SmlBinFile{ messages: ref_obj }));
        assert_eq!(buf.next(), Some(0x55));
    }
}
