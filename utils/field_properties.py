import sys


class Properties:
    def __init__(self, p: int):
        self.p = p

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


def to_le_limbs(x, size=64):
    """
    Convert a number to little endian limbs, with a certain bit size.
    """
    acc = []
    while x > 0:
        acc.append(x & ((1 << size) - 1))
        x >>= size
    return acc


def main(size: int, p: int, what_to_generate: str, as_hex: bool):
    properties = Properties(p)
    prop = getattr(properties, what_to_generate)()
    if as_hex:
        print(hex(prop))
    else:
        print(to_le_limbs(prop))


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2], 16),
         sys.argv[3], bool(sys.argv[4] if len(sys.argv) >= 5 else None))
