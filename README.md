# decaf377

Many zero-knowledge protocols require a cryptographic group that can be used
inside of an arithmetic circuit. This is accomplished by defining an “embedded”
elliptic curve whose base field is the scalar field of the proving curve used
by the proof system.

The Zexe paper, which defined BLS12-377, also defined (but did not name) a
cofactor-4 Edwards curve defined over the BLS12-377 scalar field for exactly
this purpose. However, non-prime-order groups are a leaky abstraction, forcing
all downstream constructions to pay attention to correct handling of the
cofactor. Although it is usually possible to do so safely, it requires
additional care, and as discussed below, the optimal technique for handling the
cofactor is different inside and outside of a circuit.

Instead, applying the Decaf construction to this curve gives decaf377, a clean
abstraction that provides a prime-order group, complete with hash-to-group
functionality, and works the same way inside and outside of a circuit.

More details are available on the [Penumbra
website](https://penumbra.zone/main/crypto/decaf377.html).
