//! The FP field:
//! p = 0x01ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001
//! two-adicitity = 46
//! ((p - 1) / 2^two-adicitity) (the trace)
//! c2 = 0x6b8e9185f1443ab18ec1701b28524ec688b67cc03d44e3c7bcd88bee82520005c2d7510c00000021423
//! (non square element)
//! c4 = 5 (for example)
//! c4^c2 = 0x382d3d99cdbc5d8fe9dee6aa914b0ad14fcaca7022110ec6eaa2bc56228ac41ea03d28cc795186ba6b5ef26b00bbe8

// #[cfg(feature = "arkworks")]
pub mod arkworks;
pub mod fiat;
pub mod wrapper;
