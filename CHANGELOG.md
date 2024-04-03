# 0.1.0

* Initial release.

# 0.1.1

* Fix: Disable `print-trace` feature in R1CS gadgets.

# 0.2.0

* Fix: Use compressed representation for public elements in-circuit.

# 0.3.0

* Disable internal parallelism.

# 0.4.0

* Upgrade to 0.4.x series of Arkworks dependencies.

# 0.5.0

* Audit followup:
  * Optimization: remove 7 unnecessary constraints in the R1CS sign checks.
  * Fix: Resolve incorrect handling of zero in point decompression in R1CS.

# 0.6.0

* Fix: Resolve incorrect `SubAssign` and `AddAssign` implementations in R1CS.

# 0.7.0

* Fix: Add `no_std` compatibility.

# 0.8.0

* Add fiat-generated finite field implementations by @hdevalence in #64
* refactor(arkworks): feature-gated Arkworks compatibility by @TalDerei in #67
* Implement Bls12377 using our own backend by @cronokirby in #71
* ci: add job to test u32_backend by @redshiftzero in #72
* Arkworks feature gating by @cronokirby in #73
* Implement traits in a no_std context when possible by @cronokirby in #74
* Implement the start of a minimal curve implementation by @cronokirby in #75
* ci: add job building with no alloc feature by @redshiftzero in #76
* arkworks independent projective arithmetic ops by @redshiftzero in #77
* Make modular reduction work for large byte sizes by @cronokirby in #78
* Implement FromStr for all the fields by @cronokirby in #79
* Implement a checked conversion from bytes method in Fq by @cronokirby in #81
* arkworks-independent sqrts, point encoding/decoding by @cronokirby in #80
* ci: use larger runners by @conorsch in #83
* ci: dedicated profile for release + debug_assert by @conorsch in #84
* rearranging arkworks / non-arkworks ECC code by @redshiftzero in #82

# 0.9.0

* Make raw constructors of field elements private by @cronokirby in #90
* Add missing methods as need for integrating the latest version of this crate by @cronokirby in #91
* fix: field modulus by @TalDerei in #92
* adjust anyhow scope and remove unused dependencies by @neithanmo in #96
* add power impl and expose `Fq::from_montgomery_limbs` by @redshiftzero in #98
* Add missing conversion trait implementations by @neithanmo in #97

# 0.10.0

* Move random sampling methods under `std` feature by @redshiftzero in #100
