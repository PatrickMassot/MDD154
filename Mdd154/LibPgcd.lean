import Mdd154.Lib

macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℕ Nat.instDvd ($x : ℕ) ($y : ℕ))

addAnonymousGoalSplittingLemma divise_antisym
addAnonymousFactSplittingLemma divise_pgcd_si
addAnonymousFactSplittingLemma divise_refl
addAnonymousFactSplittingLemma divise_si_divise_pgcd
addAnonymousFactSplittingLemma divise_si_divise_left
addAnonymousFactSplittingLemma divise_si_divise_right

addAnonymousComputeLemma pgcd_divise_left
addAnonymousComputeLemma pgcd_divise_right

addAnonymousFactSplittingLemma pgcd_divise_left
addAnonymousFactSplittingLemma pgcd_divise_right
addAnonymousFactSplittingLemma divise_antisym
