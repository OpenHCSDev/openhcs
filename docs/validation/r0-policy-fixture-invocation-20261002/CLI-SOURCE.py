from dataclasses import dataclass
@dataclass
class Record:
    alpha: str
    beta: int
    gamma: str

def check(row: Record):
    return isinstance(row.beta, int)
