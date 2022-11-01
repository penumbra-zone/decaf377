use ark_ed_on_bls12_377::constraints::FqVar;

pub trait FqVarExtension {
    fn abs(&self) -> FqVar;
    fn isqrt(&self) -> FqVar;
}

impl FqVarExtension for FqVar {
    // Remove this in favor of impl Sign for FqVar
    fn abs(&self) -> FqVar {
        todo!()
    }

    fn isqrt(&self) -> FqVar {
        // Out of circuit sqrt computation
        // Add constraints in circuit
        todo!()
    }
}

// impl Sign for FqVar
