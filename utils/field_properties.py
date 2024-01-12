import sys

GENERATORS = {
    0x01ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001: 15
}


class Properties:
    def __init__(self, p: int):
        self.p = p

    def one(self):
        return 1

    def modulus(self):
        return self.p

    def modulus_plus_1(self):
        return self.p + 1

    def modulus_bit_size(self):
        return self.p.bit_length()

    def two_adicity(self) -> int:
        """
        Calculate the two-adicity of this field.
        """
        acc = self.p - 1
        count = 0
        while acc & 1 == 0:
            count += 1
            acc >>= 1
        return count

    def trace(self):
        """
        (self - 1) / 2^two_adicity
        """
        return (self.p - 1) >> self.two_adicity()

    def trace_minus_one_div_two(self):
        return (self.trace() - 1) >> 1

    def mod_exp(self, a, e):
        insert = a
        acc = 1
        while e != 0:
            if e & 1 == 1:
                acc = acc * insert % self.p
            insert = (insert * insert) % self.p
            e = e >> 1
        return acc

    def legendre_symbol(self, x):
        return self.mod_exp(x, (self.p - 1) >> 1)

    def quadratic_non_residue(self):
        acc = 1
        while self.legendre_symbol(acc) == 1:
            acc += 1
        return acc

    def quadratic_non_residue_to_trace(self):
        return self.mod_exp(self.quadratic_non_residue(), self.trace())

    def modulus_minus_one_div_two(self):
        return ((self.p - 1) >> 1)

    def generator(self):
        if self.p in GENERATORS:
            return GENERATORS[self.p]
        raise ValueError(f"no known generator for {hex(self.p)}")

    def two_adic_root_of_unity(self):
        return self.mod_exp(self.generator(), self.trace())


def to_le_limbs(x, size=64):
    """
    Convert a number to little endian limbs, with a certain bit size.
    """
    acc = []
    while x > 0:
        acc.append(x & ((1 << size) - 1))
        x >>= size
    return acc


def to_monty(x, size, p):
    shift = len(to_le_limbs(p - 1, size)) * size
    return (x << shift) % p


def main(size: int, p: int, what_to_generate: str, mode):
    properties = Properties(p)
    prop = getattr(properties, what_to_generate)
    if callable(prop):
        prop = prop()
    if mode == "hex":
        print(hex(prop))
    elif mode == "monty":
        print(to_le_limbs(to_monty(prop, size, p), size))
    elif mode == "monty_hex":
        print(hex(to_monty(prop, size, p)))
    else:
        print(to_le_limbs(prop, size))


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2], 16),
         sys.argv[3], sys.argv[4] if len(sys.argv) >= 5 else None)
