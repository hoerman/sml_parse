/* Todo: - throw error in the msg splitting functions if list to split
 *         contains unexpected additional elements
 */
use crate::SmlError;
use crate::SmlBinFile;
use crate::SmlFile;
use crate::Result;
use crate::sml_unit::SmlUnit;
use crate::sml_bin_parse::SmlBinElement;
use crate::sml_bin_parse::SmlBinElement::*;

use SmlMessageBody::*;

const MSG_ID_OPEN_RES: u32 = 0x0101;
const MSG_ID_CLOSE_RES: u32 = 0x0201;
const MSG_ID_LIST_RES: u32 = 0x0701;

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
    AbortAfterGroup,
    Abort,
}

#[derive(Debug, PartialEq)]
pub enum SmlMessageBody {
    OpenRes(SmlOpenRes),
    CloseRes(SmlCloseRes),
    ListRes(SmlListRes),
}

#[derive(Debug, PartialEq)]
pub struct SmlOpenRes {
    codepage: Option<Vec<u8>>,
    client_id: Option<Vec<u8>>,
    req_file_id: Vec<u8>,
    server_id: Vec<u8>,
    ref_time: Option<SmlTime>,
    sml_version: Option<u8>,
}

#[derive(Debug, PartialEq)]
pub enum SmlTime {
    SecIndex(u32),  // [s]
    TimeStamp(u32), // [s] since 01.01.1970 0:00
    LocalTimeStamp { timestamp: u32,         // [s] since 01.01.1970 0:00
                     local_offset: i16,      // [min]
                     season_time_offset: i16 // [min]
    },
}

#[derive(Debug, PartialEq)]
pub struct SmlCloseRes {
    global_signature: Option<Vec<u8>>
}

#[derive(Debug, PartialEq)]
pub struct SmlListRes {
    client_id: Option<Vec<u8>>,
    server_id: Vec<u8>,
    list_name: Option<Vec<u8>>,
    act_sensor_time: Option<SmlTime>,
    val_list: Vec<SmlListEntry>,
    list_signature: Option<Vec<u8>>,
    act_gateway_time: Option<SmlTime>,
}

#[derive(Debug, PartialEq)]
pub struct SmlListEntry {
    obj_name: Vec<u8>,
    status: Option<SmlStatus>,
    val_time: Option<SmlTime>,
    unit: Option<SmlUnit>,
    scaler: Option<i8>,
    value: SmlValue,
    value_signature: Option<Vec<u8>>,
}

#[derive(Debug, PartialEq)]
pub enum SmlStatus {
    Status8(u8),
    Status16(u16),
    Status32(u32),
    Status64(u64),
}

#[derive(Debug, PartialEq)]
pub enum SmlValue {
    BoolVal(bool),
    ByteList(Vec<u8>),
    Int8Val(i8),
    Int16Val(i16),
    Int32Val(i32),
    Int64Val(i64),
    UInt8Val(u8),
    UInt16Val(u16),
    UInt32Val(u32),
    UInt64Val(u64),
    SmlList(SmlListType),
}

#[derive(Debug, PartialEq)]
pub enum SmlListType {
    SmlTime(SmlTime),
}

trait MessageListIter : Iterator {
    fn next_el(&mut self) -> Result<Self::Item>
    {
        self.next().ok_or(SmlError::InvalidSmlMsgStructure)
    }

    fn last_el(&mut self) -> Result<Self::Item>
    {
        let el = self.next_el()?;

        match self.next() {
            None => Ok(el),
            _ => Err(SmlError::InvalidSmlMsgStructure)
        }
    }
}

impl<T> MessageListIter for std::vec::IntoIter<T> {}

pub fn bin_file_to_sml(bin: SmlBinFile) -> Result<SmlFile>
{
    let mut el_iter = bin.messages.into_iter();

    let _open_res = read_open_el(el_iter.next()
                                .ok_or(SmlError::MissingSmlOpenMsg)?)?;

    Err(SmlError::MissingSmlOpenMsg)
}

fn read_open_el(el: SmlBinElement) -> Result<SmlMessage>
{
    let _msg = sml_bin_element_to_message(el)?;
    
    //    match bin_element_to_message(el) {}
    Err(SmlError::MissingSmlOpenMsg)
}

fn sml_bin_element_to_message(el: SmlBinElement) -> Result<SmlMessage>
{
    if let SmlBinElement::List(msg_list) = el {
        let (seq, group, abort_on_err, msg, crc) = split_msg_list(msg_list)?;

        build_sml_msg(seq, group, abort_on_err, msg, crc)
    } else {
        Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn split_msg_list(list: Vec<SmlBinElement>) -> Result<(Vec<u8>, u8, u8,
                                                       Vec<SmlBinElement>, u16)>
{
    let mut li = list.into_iter();
    let (seq_el, group_el, abort_on_error_el, msg_el, crc_el, eom) =
        (li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.next_el()?);
         
    match (seq_el, group_el, abort_on_error_el, msg_el, crc_el, eom) {
        (OctetString(seq), U8(group), U8(abort_on_error),
         List(msg), U16(crc), EndOfMsg) =>
            Ok((seq, group, abort_on_error, msg, crc)),
        _ => Err(SmlError::InvalidSmlMsgStructure),
    }
}

fn build_sml_msg(seq: Vec<u8>, group: u8, abort_on_err_val: u8,
                 msg: Vec<SmlBinElement>, crc: u16) -> Result<SmlMessage>
{
    let abort_on_err = abort_on_error_from_u8(abort_on_err_val)?;

    let (msg_id, msg_body_vec) = split_msg_body(msg)?;
    let msg_body = build_msg_body(msg_id, msg_body_vec)?;
    
    Ok(SmlMessage { transaction_id: seq, group_no: group,
                    abort_on_error: abort_on_err, message_body: msg_body,
                    crc16: crc })
}

fn abort_on_error_from_u8(val: u8) -> Result<AbortOnError>
{
    match val {
        0x00 => Ok(AbortOnError::Continue),
        0x01 => Ok(AbortOnError::SkipGroup),
        0x02 => Ok(AbortOnError::AbortAfterGroup),
        0xff => Ok(AbortOnError::Abort),
        _ => Err(SmlError::UnknownAbortOnErrorVal(val))
    }
}

fn split_msg_body(msg_body: Vec<SmlBinElement>)
    -> Result<(u32, Vec<SmlBinElement>)>
{
    let mut bi = msg_body.into_iter();
    let (id_el, body_el) = (bi.next_el()?,
                            bi.next_el()?);

    match (id_el, body_el) {
        (U8(id_el), List(msg)) => Ok((id_el as u32, msg)),
        (U16(id_el), List(msg)) => Ok((id_el as u32, msg)),
        (U32(id_el), List(msg)) => Ok((id_el, msg)),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn build_msg_body(msg_id: u32,
                  body_list: Vec<SmlBinElement>) -> Result<SmlMessageBody>
{
    match msg_id {
        MSG_ID_OPEN_RES => build_open_res_msg_body(body_list),
        _ => Err(SmlError::UnknownMsgId(msg_id)),
    }
}

fn build_open_res_msg_body(body_list: Vec<SmlBinElement>)
    -> Result<SmlMessageBody>
{
    let mut li = body_list.into_iter();
    let (codepage_el, client_id_el, req_file_id_el,
         server_id_el, ref_time_el, sml_version_el) =
        (li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.next_el()?,
         li.last_el()?);

    let codepage = octet_str_option_from_el(codepage_el)?;
    let client_id = octet_str_option_from_el(client_id_el)?;
    let req_file_id = octet_str_from_el(req_file_id_el)?;
    let server_id = octet_str_from_el(server_id_el)?;
    let ref_time = time_option_from_el(ref_time_el)?;
    let sml_version = u8_option_from_el(sml_version_el)?;

    Ok(OpenRes(
        SmlOpenRes {
            codepage: codepage,
            client_id: client_id,
            req_file_id: req_file_id,
            server_id: server_id,
            ref_time: ref_time,
            sml_version: sml_version
        })
    )
}

fn octet_str_option_from_el(el: SmlBinElement) -> Result<Option<Vec<u8>>>
{
    let vec = octet_str_from_el(el)?;

    if vec.len() != 0 {
        Ok(Some(vec))
    } else {
        Ok(None)
    }
}

fn octet_str_from_el(el: SmlBinElement) -> Result<Vec<u8>>
{
    if let OctetString(vec) = el {
        Ok(vec)
    } else {
        Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn time_option_from_el(el: SmlBinElement) -> Result<Option<SmlTime>>
{
    match el {
        List(list) => Ok(Some(time_from_list(list)?)),
        OctetString(ostr) if ostr.len() == 0 => Ok(None),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn time_from_list(list: Vec<SmlBinElement>) -> Result<SmlTime>
{
    let mut li = list.into_iter();
    let (time_type_el, time_el) =
        (li.next_el()?,
         li.last_el()?);

    match (time_type_el, time_el) {
        (U8(tt), U32(t)) if tt == 0x01 => Ok(SmlTime::SecIndex(t)),
        (U8(tt), U32(t)) if tt == 0x02 => Ok(SmlTime::TimeStamp(t)),
        (U8(tt), List(tl)) if tt == 0x03 =>
            time_local_timestamp_from_list(tl),
        (U8(tt), _) if tt > 0x03 => Err(SmlError::UnknownTimeFormat(tt)),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn time_local_timestamp_from_list(list: Vec<SmlBinElement>) -> Result<SmlTime>
{
    let mut li = list.into_iter();
    let (timestamp_el, local_offset_el, season_time_offset_el) =
        (li.next_el()?,
         li.next_el()?,
         li.last_el()?);

    match (timestamp_el, local_offset_el, season_time_offset_el) {
        (U32(ts), I16(l_offs), I16(season_offs)) =>
            Ok(SmlTime::LocalTimeStamp { timestamp: ts,
                                         local_offset: l_offs,
                                         season_time_offset: season_offs,
            }),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}
            
fn u8_option_from_el(el: SmlBinElement) -> Result<Option<u8>>
{
    match el {
        U8(val) => Ok(Some(val)),
        OctetString(ostr) if ostr.len() == 0 => Ok(None),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_u8_option_from_el_has_u8()
    {
        assert_eq!(u8_option_from_el(U8(5)).unwrap(), Some(5));
    }

    #[test]
    fn t_u8_option_from_el_none()
    {
        assert_eq!(u8_option_from_el(OctetString(vec![])).unwrap(), None);
    }

    #[test]
    fn t_u8_option_from_el_wrong_el()
    {
        assert_eq!(u8_option_from_el(U16(5)),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_time_option_from_el_sec_index()
    {
        let el = List(vec![U8(0x01), U32(0x1234_8765)]);

        assert_eq!(time_option_from_el(el).unwrap(),
                   Some(SmlTime::SecIndex(0x1234_8765)));
    }

    #[test]
    fn t_time_option_from_el_time_stamp()
    {
        let el = List(vec![U8(0x02), U32(0x4321_8765)]);

        assert_eq!(time_option_from_el(el).unwrap(),
                   Some(SmlTime::TimeStamp(0x4321_8765)));
    }

    #[test]
    fn t_time_option_from_el_local_time_stamp()
    {
        let el = List(vec![U8(0x03),
                           List(vec![U32(0x8765_1234), I16(2), I16(-1)])]);

        assert_eq!(time_option_from_el(el).unwrap(),
                   Some(SmlTime::LocalTimeStamp{
                       timestamp: 0x8765_1234,
                       local_offset: 2,
                       season_time_offset: -1
                   }));
    }

    #[test]
    fn t_time_option_from_el_none()
    {
        assert_eq!(time_option_from_el(OctetString(vec![])).unwrap(), None);
    }

    #[test]
    fn t_time_option_from_el_unkown_time_format()
    {
        let el = List(vec![U8(0x04), U32(0x1234_8765)]);

        assert_eq!(time_option_from_el(el),
                   Err(SmlError::UnknownTimeFormat(0x04)));
    }

    #[test]
    fn t_time_option_from_el_invalid_structure_on_known_format()
    {
        let el = List(vec![U8(0x01), U16(0x8765)]);

        assert_eq!(time_option_from_el(el),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_time_option_from_el_long_list_on_known_format()
    {
        let el = List(vec![U8(0x01), U32(2), U16(0x8765)]);

        assert_eq!(time_option_from_el(el),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_time_option_from_el_local_time_stamp_long_list()
    {
        let el = List(vec![U8(0x03),
                           List(vec![U32(0x8765_1234), I16(2), I16(-1), U8(1)])]);

        assert_eq!(time_option_from_el(el),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_octet_str_from_el()
    {
        assert_eq!(octet_str_from_el(OctetString(vec![])).unwrap(),
                   vec![]);

        assert_eq!(octet_str_from_el(OctetString(vec![0x01, 0x02])).unwrap(),
                   vec![0x01, 0x02]);
    }

    #[test]
    fn t_octet_str_from_el_wrong_element()
    {
        assert_eq!(octet_str_from_el(U8(5)),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_octet_str_option_from_el()
    {
        assert_eq!(
            octet_str_option_from_el(OctetString(vec![0x01, 0x02])).unwrap(),
            Some(vec![0x01, 0x02])
        );
    }

    #[test]
    fn t_octet_str_option_from_el_none()
    {
        assert_eq!(octet_str_option_from_el(OctetString(vec![])).unwrap(), None);
    }

    #[test]
    fn t_octet_str_option_from_el_wrong_element()
    {
        assert_eq!(octet_str_option_from_el(List(vec![])),
                   Err(SmlError::InvalidSmlMsgStructure));
    }

    #[test]
    fn t_build_open_res_msg_body()
    {
        let list = vec![
            OctetString(vec![0x01]),
            OctetString(vec![0x04, 0x03, 0x02, 0x01]),
            OctetString(vec![0x05, 0x06, 0x07, 0x08]),
            OctetString(vec![0x10, 0x20, 0x30, 0x40]),
            List(vec![U8(0x01), U32(0x1234_5678)]),
            U8(0x01)
        ];

        assert_eq!(build_open_res_msg_body(list).unwrap(),
                   OpenRes(SmlOpenRes {
                       codepage: Some(vec![0x01]),
                       client_id: Some(vec![0x04, 0x03, 0x02, 0x01]),
                       req_file_id: vec![0x05, 0x06, 0x07, 0x08],
                       server_id: vec![0x10, 0x20, 0x30, 0x40],
                       ref_time: Some(SmlTime::SecIndex(0x1234_5678)),
                       sml_version: Some(0x01),
                    }));
    }

    #[test]
    fn t_build_open_res_msg_body_all_optional()
    {
        let list = vec![
            OctetString(vec![]),
            OctetString(vec![]),
            OctetString(vec![0x15, 0x06, 0x27, 0x08]),
            OctetString(vec![0x10, 0x20, 0x33, 0x40, 0x55]),
            OctetString(vec![]),
            OctetString(vec![])
        ];

        assert_eq!(build_open_res_msg_body(list).unwrap(),
                   OpenRes(SmlOpenRes {
                       codepage: None,
                       client_id: None,
                       req_file_id: vec![0x15, 0x06, 0x27, 0x08],
                       server_id: vec![0x10, 0x20, 0x33, 0x40, 0x55],
                       ref_time: None,
                       sml_version: None,
                    }));

    }

    #[test]
    fn t_build_open_res_msg_body_long_list()
    {
        let list = vec![
            OctetString(vec![]),
            OctetString(vec![]),
            OctetString(vec![0x15, 0x06, 0x27, 0x08]),
            OctetString(vec![0x10, 0x20, 0x33, 0x40, 0x55]),
            OctetString(vec![]),
            OctetString(vec![]),
            OctetString(vec![])
        ];

        assert_eq!(build_open_res_msg_body(list),
                   Err(SmlError::InvalidSmlMsgStructure));
    }
}

