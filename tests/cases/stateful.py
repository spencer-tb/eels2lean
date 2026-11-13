"""
Functions for the differential check that EELS does not have.

They are translated and checked like EELS functions. Each one is here for
behavior that no checked EELS function reaches.
"""

from dataclasses import dataclass

from ethereum_types.numeric import Uint


@dataclass
class Budget:
    """An amount left to spend, and the amount spent so far."""

    left: Uint
    spent: Uint


def spend(budget: Budget, amount: Uint) -> None:
    """
    Record a spend, then take it from what is left.

    When `amount` is more than `left`, the subtraction raises after
    `spent` was written. The write has to survive the raise.
    """
    budget.spent += amount
    budget.left -= amount
