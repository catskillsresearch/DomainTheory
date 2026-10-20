module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_INCL
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_ofPresentation_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_toNbhd_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconstruct
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconElem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconElemInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Round-trip B (the isomorphism).** `reconElem`/`reconElemInv` are mutually inverse and preserve
and reflect the approximation order, giving `|V| ≃o |toSystem (ofPresentation P)|`. -/
def reconIso (P : ComputablePresentation V) : V.Element ≃o (reconstruct P).Element where
  toFun := reconElem P
  invFun := reconElemInv P
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨n, rfl, m, hWm, hxm⟩
      rw [ofPresentation_toNbhd_eq_iff] at hWm
      rw [hWm]; exact hxm
    · intro hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      exact ⟨n, hn.symm, n, rfl, by rw [hn]; exact hxW⟩
  right_inv := by
    intro y
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, rfl, m, hXm, hym⟩
      have : (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m :=
        (ofPresentation_toNbhd_eq_iff P n m).mpr hXm
      rw [this]; exact hym
    · intro hyT
      obtain ⟨n, hn⟩ := y.sub hyT
      exact ⟨n, hn, n, rfl, by rw [← hn]; exact hyT⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      have hmem : (reconElem P x).mem ((ofPresentation P).toNbhd n) :=
        ⟨n, rfl, by rw [hn]; exact hxW⟩
      obtain ⟨m, hm, hx'm⟩ := h ((ofPresentation P).toNbhd n) hmem
      rw [ofPresentation_toNbhd_eq_iff] at hm
      rw [← hn, hm]; exact hx'm
    · intro h Y hY
      obtain ⟨n, rfl, hxn⟩ := hY
      exact ⟨n, rfl, h (P.X n) hxn⟩

end DomainTheory.NeighbourhoodSystems.Exercise713
