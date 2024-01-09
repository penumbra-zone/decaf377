import sys


class Properties:
    def __init__(self, p: int):
        self.p = p

    def one(self):
        return 1

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
