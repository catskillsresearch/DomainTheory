module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section

abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem
end

section

def botElt : T.Element := Example12.neighborhoodSystem.bot
end

section

theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem
end

section

def falseElt : T.Element := Example12.neighborhoodSystem.elemOne
end

section

def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)
end

section
@[simp] theorem scan_nil : scan [] = none := rfl
end

section
@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl
end

section
@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl
end

section

theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl
end

section

def trueElt : T.Element := Example12.neighborhoodSystem.elemZero
end

section

def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt
end

section

theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]
end

section

def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    show (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩
end

section

theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  Example12.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1
end

section

theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩
end

section

theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩
end

section

theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩
end

section

theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]
end

section

theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]
end

section

theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ
end

end DomainTheory.NeighbourhoodSystems.Example23
