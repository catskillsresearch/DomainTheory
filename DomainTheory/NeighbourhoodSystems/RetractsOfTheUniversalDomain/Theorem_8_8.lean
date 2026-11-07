module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixedNbhdEffective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UConstructs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIsoCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

theorem theorem_8_8_a {α : Type*} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] :
    ∃ D' : NeighborhoodSystem ℚ, (D ≅ᴰ D') ∧ (D' ◁ U) := by
  have : Nonempty {S : Set α // D.mem S} := ⟨⟨D.master, D.master_mem⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat {S : Set α // D.mem S}
  set e : ℕ → Set α := fun n => if n = 0 then D.master else (f (n - 1)).1 with hedef
  have he0 : e 0 = D.master := ite_eq_left rfl
  have hen : ∀ n, e (n + 1) = (f n).1 := by
    intro n
    show (if n + 1 = 0 then D.master else (f (n + 1 - 1)).1) = (f n).1
    rw [ite_eq_right (Nat.succ_ne_zero n), Nat.succ_sub_one]
  have hcover : ∀ S, D.mem S ↔ ∃ n, S = e n := by
    intro S
    constructor
    · intro hS
      obtain ⟨k, hk⟩ := hf ⟨S, hS⟩
      exact ⟨k + 1, by rw [hen k]; exact (congrArg Subtype.val hk).symm⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => rw [he0]; exact D.master_mem
      | succ n => rw [hen n]; exact (f n).2
  exact ⟨DprimeU D e hcover he0, isomorphic_DprimeU D e hcover he0, DprimeU_subsystem D e hcover he0⟩

theorem theorem_8_8 {α : Type*} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

theorem theorem_8_8_b {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (D' : NeighborhoodSystem ℚ) (P' : ComputablePresentation D') (h : D' ◁ U),
      (D ≅ᴰ D') ∧
        ComputableMap P' UComputablePresentation h.inj ∧
        ComputableMap UComputablePresentation P' h.proj :=
  ⟨DprimeUCode P, DprimeUCodePresentation P, DprimeUCode_subsystem P,
    isomorphic_DprimeUCode P, DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

theorem theorem_8_8_c {a : ApproximableMap U U} (_hfin : FinitaryProjection a)
    (hcomp : ComputableMap UComputablePresentation UComputablePresentation a) :
    (fixedNbhd a).IsEffectivelyGiven ∧ fixedNbhd a ◁ U :=
  ⟨fixedNbhd_isEffectivelyGiven hcomp, fixedNbhd_subsystem a⟩

theorem theorem_8_8_b_strong {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (i : ApproximableMap D U) (j : ApproximableMap U D),
      j.comp i = idMap D ∧ i.comp j ≤ idMap U ∧
        ComputableMap P UComputablePresentation i ∧
        ComputableMap UComputablePresentation P j := by
  set h := DprimeUCode_subsystem P with hh
  refine ⟨h.inj.comp (isoInj P), (isoProj P).comp h.proj, ?_, ?_, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc h.proj h.inj (isoInj P), h.proj_comp_inj, idMap_comp]
    exact isoProj_comp_isoInj P
  · have heq : (h.inj.comp (isoInj P)).comp ((isoProj P).comp h.proj) = h.inj.comp h.proj := by
      rw [comp_assoc, ← comp_assoc (isoInj P) (isoProj P) h.proj, isoInj_comp_isoProj, idMap_comp]
    rw [heq]
    exact h.inj_comp_proj_le
  · exact comp_isComputable (isoInj_isComputableMap P) (DprimeUCode_inj_isComputableMap P)
  · exact comp_isComputable (DprimeUCode_proj_isComputableMap P) (isoProj_isComputableMap P)

end DomainTheory.NeighbourhoodSystems
