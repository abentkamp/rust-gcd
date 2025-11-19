-- This module serves as the root of the `Gcd` library.
-- Import modules here that should be built as part of the library.
import Gcd.Funs

open Aeneas.Std Result Error
namespace gcd

attribute [scalar_tac_simps] bne_iff_ne

@[progress]
theorem euclid_loop_u8_spec (a b : U8) :
    ∃ y, euclid_u8_loop a b = ok y := by
  unfold euclid_u8_loop
  progress*
termination_by b.val
decreasing_by scalar_tac

theorem euclid_u8_spec (a b : U8) :
    ∃ y, euclid_u8 a b = ok y := by
  unfold euclid_u8
  progress*

axiom trailing_zeros : U8 → U32

@[progress]
theorem trailing_zeros_spec (v : U8) (hv : v ≠ 0#u8):
  ∃ y, core.num.U8.trailing_zeros v = .ok y ∧ y < 8#u32 ∧ y = trailing_zeros v := sorry

@[progress]
theorem shift_right_spec (u : U8) (v : U32) (hu : u ≠ 0#u8) (hv : v ≤ trailing_zeros u):
  ∃ y, u >>> v = .ok y ∧ y ≠ 0#u8 ∧ y ≤ u := sorry

@[progress]
theorem bor_spec (u v : U8) (hu : u ≠ 0#u8) (hv : v ≠ 0#u8) :
  ∃ y, (↑(u ||| v) : Result U8) = .ok y ∧
    trailing_zeros y ≤ trailing_zeros u ∧
    trailing_zeros y ≤ trailing_zeros v ∧
    y ≠ 0#u8 := sorry

@[progress]
theorem binary_u8_loop_spec (a b : U8) (ha : a ≠ 0#u8) (hb : b ≠ 0#u8):
    ∃ y, binary_u8_loop a b = ok y ∧ y ≠ 0#u8 := by
  unfold binary_u8_loop
  progress*
termination_by a.val + b.val
decreasing_by all_goals scalar_tac

theorem binary_u8_spec (a b : U8) :
    ∃ y, binary_u8 a b = ok y := by
  unfold binary_u8
  progress*
