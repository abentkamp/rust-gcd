import GcdVerif.Gcd
open Aeneas.Std Result Error
namespace gcd

theorem euclid_loop0_u8_spec (a b : U8)
  : ∃ y, euclid_u8_loop0 a b = ok y
  := by
  unfold euclid_u8_loop0
  split
  case isTrue h =>
    have : b ≠ 0#u8 := by grind
    progress as ⟨ c ⟩
    progress
  case isFalse h =>
    simp
termination_by b
decreasing_by sorry
