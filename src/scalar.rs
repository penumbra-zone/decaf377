/// `Scalar` Represents an integer value.
pub struct Scalar {
    bytes: [u8; 32],
}

// For Scalar we will:
// * impl Zeroize since the scalars (generally) are secret values
// * what else?
