import sys


class Properties:
    def __init__(self, p: int):
        self.p = p

    def two_adicity(self) -> int:
        return (1 << 64) | 2


def to_le_limbs(x, size=64):
    """
    Convert a number
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
