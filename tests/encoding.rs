use std::convert::TryFrom;

use proptest::prelude::*;

use decaf377::{basepoint, Element, Encoding, FieldExt, Fr};

#[test]
fn identity_encoding_is_zero() {
    let identity = Element::default();
    let identity_bytes = identity.vartime_compress();
    assert_eq!(identity_bytes.0, [0; 32]);
    let identity2 = identity_bytes.vartime_decompress().unwrap();
    assert_eq!(identity, identity2);
}

#[test]
fn check_generator() {
    let mut bytes = [0u8; 32];

    for b in 1..=255 {
        bytes[0] = b;
        if let Ok(_element) = Encoding(bytes).vartime_decompress() {
            break;
        }
    }

    // The generator [8,0,...] is minimal
    assert_eq!(bytes[0], 8);

    let enc2 = Encoding(bytes)
        .vartime_decompress()
        .unwrap()
        .vartime_compress();
    assert_eq!(bytes, enc2.0);

    assert_eq!(Encoding(bytes).vartime_decompress().unwrap(), basepoint());
}

#[test]
fn test_encoding_matches_sage_encoding() {
    use hex;

    let mut accumulator = Element::default();
    let basepoint = basepoint();

    let expected_points = [
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0800000000000000000000000000000000000000000000000000000000000000",
        "b2ecf9b9082d6306538be73b0d6ee741141f3222152da78685d6596efc8c1506",
        "2ebd42dd3a2307083c834e79fb9e787e352dd33e0d719f86ae4adb02fe382409",
        "6acd327d70f9588fac373d165f4d9d5300510274dffdfdf2bf0955acd78da50d",
        "460f913e516441c286d95dd30b0a2d2bf14264f325528b06455d7cb93ba13a0b",
        "ec8798bcbb3bf29329549d769f89cf7993e15e2c68ec7aa2a956edf5ec62ae07",
        "48b01e513dd37d94c3b48940dc133b92ccba7f546e99d3fc2e602d284f609f00",
        "a4e85dddd19c80ecf5ef10b9d27b6626ac1a4f90bd10d263c717ecce4da6570a",
        "1a8fea8cbfbc91236d8c7924e3e7e617f9dd544b710ee83827737fe8dc63ae00",
        "0a0f86eaac0c1af30eb138467c49381edb2808904c81a4b81d2b02a2d7816006",
        "588125a8f4e2bab8d16affc4ca60c5f64b50d38d2bb053148021631f72e99b06",
        "f43f4cefbe7326eaab1584722b1b4860de554b23a14490a03f3fd63a089add0b",
        "76c739a33ffd15cf6554a8e705dc573f26490b64de0c5bd4e4ac75ed5af8e60b",
        "200136952d18d3f6c70347032ba3fef4f60c240d706be2950b4f42f1a7087705",
        "bcb0f922df1c7aa9579394020187a2e19e2d8073452c6ab9b0c4b052aa50f505",
    ];

    for hexstr in expected_points {
        let bytes = hex::decode(hexstr).unwrap();
        let point = Encoding::try_from(bytes.as_slice())
            .unwrap()
            .vartime_decompress()
            .unwrap();

        let result_hexstr = hex::encode(point.vartime_compress().0);

        assert_eq!(result_hexstr.as_str(), hexstr);

        assert_eq!(accumulator, point);

        accumulator += basepoint;
    }
}

proptest! {
    #[test]
    fn group_encoding_round_trip_if_successful(bytes: [u8; 32]) {
        let bytes = Encoding(bytes);

        if let Ok(element) = bytes.vartime_decompress() {
            let bytes2 = element.vartime_compress();
            assert_eq!(bytes, bytes2);
        }
    }

    #[test]
    fn scalar_encoding_round_trip_if_successful(bytes: [u8; 32]) {
        if let Ok(x) = Fr::from_bytes(bytes) {
            let bytes2 = x.to_bytes();
            assert_eq!(bytes, bytes2);
        }
    }
}
