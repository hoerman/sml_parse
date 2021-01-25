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
    AbortAfterGrop,
    Abort,
}

pub enum SmlMessageBody {
    OpenRes(SmlOpenRes),
    CloseRes(SmlCloseRes),
    ListRes(SmlListRes),
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
    SecIndex(u32),  // [s]
    TimeStamp(u32), // [s] since 01.01.1970 0:00
    LocalTimeStamp { timestamp: u32,         // [s] since 01.01.1970 0:00
                     local_offset: i16,      // [min]
                     season_time_offset: i16 // [min]
    },
}

pub struct SmlCloseRes {
    global_signature: Option<Vec<u8>>
}

pub struct SmlListRes {
    client_id: Option<Vec<u8>>,
    server_id: Vec<u8>,
    list_name: Option<Vec<u8>>,
    act_sensor_time: Option<SmlTime>,
    val_list: Vec<SmlListEntry>,
    list_signature: Option<Vec<u8>>,
    act_gateway_time: Option<SmlTime>,
}

pub struct SmlListEntry {
    obj_name: Vec<u8>,
    status: Option<SmlStatus>,
    val_time: Option<SmlTime>,
    unit: Option<SmlUnit>,
    scaler: Option<i8>,
    value: SmlValue,
    value_signature: Option<Vec<u8>>,
}

pub enum SmlStatus {
    Status8(u8),
    Status16(u16),
    Status32(u32),
    Status64(u64),
}

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

pub enum SmlListType {
    SmlTime(SmlTime),
}
    
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
        (li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?);
         
    match (seq_el, group_el, abort_on_error_el, msg_el, crc_el, eom) {
        (OctetString(seq), U8(group), U8(abort_on_error),
         List(msg), U16(crc), EndOfMsg) =>
            Ok((seq, group, abort_on_error, msg, crc)),
        _ => Err(SmlError::InvalidSmlMsgStructure),
    }
}

fn build_sml_msg(_seq: Vec<u8>, _group: u8, _abort_on_err: u8,
                 msg: Vec<SmlBinElement>, _crc: u16) -> Result<SmlMessage>
{
    let (msg_id, msg_body_vec) = split_msg_body(msg)?;

    let _msg_body = build_msg_body(msg_id, msg_body_vec)?;
    
    Err(SmlError::InvalidSmlMsgStructure)
}

fn split_msg_body(msg_body: Vec<SmlBinElement>)
    -> Result<(u32, Vec<SmlBinElement>)>
{
    let mut bi = msg_body.into_iter();
    let (id_el, body_el) = (bi.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
                            bi.next().ok_or(SmlError::InvalidSmlMsgStructure)?);

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
        (li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?);

    let codepage = octet_str_option_from_el(codepage_el)?;
    let client_id = octet_str_option_from_el(client_id_el)?;
    let req_file_id = octet_str_from_el(req_file_id_el)?;
    let server_id = octet_str_from_el(server_id_el)?;
    let ref_time = time_option_from_el(ref_time_el)?;
    let sml_version = u8_option_from_el(sml_version_el)?;

    Ok(SmlMessageBody::OpenRes(
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
        (li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?);

    match (time_type_el, time_el) {
        (U8(tt), U32(t)) if tt == 0x01 => Ok(SmlTime::SecIndex(t)),
        (U8(tt), U32(t)) if tt == 0x02 => Ok(SmlTime::TimeStamp(t)),
        (U8(tt), List(tl)) if tt == 0x03 => time_local_timestamp_from_list(tl),
        (U8(tt), _) => Err(SmlError::UnknownTimeFormat(tt)),
        _ => Err(SmlError::InvalidSmlMsgStructure)
    }
}

fn time_local_timestamp_from_list(list: Vec<SmlBinElement>) -> Result<SmlTime>
{
    let mut li = list.into_iter();
    let (timestamp_el, local_offset_el, season_time_offset_el) =
        (li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?,
         li.next().ok_or(SmlError::InvalidSmlMsgStructure)?);

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

