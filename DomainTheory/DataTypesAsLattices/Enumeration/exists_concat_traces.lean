module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_left
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_right
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_append
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_empty

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem exists_concat_traces {c : ℕ} (ks : List ℕ)
    (h : ∀ i ∈ ks, ∃ tr, valTraceOk tr ∧ valTraceHas tr c i) :
    ∃ tr, valTraceOk tr ∧ ∀ i ∈ ks, valTraceHas tr c i := by
  induction ks with
  | nil => exact ⟨[], valTraceOk_empty, fun _ hi => by simp at hi⟩
  | cons i is ih =>
      obtain ⟨tr₁, hok₁, hhas₁⟩ := h i (by simp)
      obtain ⟨tr₂, hok₂, hhas₂⟩ := ih fun j hj => h j (by simp [hj])
      refine ⟨tr₁ ++ tr₂, valTraceOk_append hok₁ hok₂, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact valTraceHas_append_left hhas₁
      · exact valTraceHas_append_right (hhas₂ j hj)

end DomainTheory.DataTypesAsLattices
