module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.TwoTokenElements
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Truth
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom

abbrev T : NeighborhoodSystem TwoToken.Token := TwoToken.neighborhoodSystem

def botElt : T.Element := TwoToken.neighborhoodSystem.bot

theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = TwoToken.master := hZ
  subst this
  exact x.master_mem

def falseElt : T.Element := TwoToken.neighborhoodSystem.elemOne

def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

@[simp] theorem scan_nil : scan [] = none := rfl

@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl

@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl

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

def trueElt : T.Element := TwoToken.neighborhoodSystem.elemZero

def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone.nil.symm, ?_⟩
    show (botElt).mem TwoToken.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone.injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone.subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  TwoToken.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1

theorem parityMap_rel_cone (σ : Str) (Y : Set TwoToken.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone.injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set TwoToken.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set TwoToken.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone.subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]

theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]

theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

end DomainTheory.NeighbourhoodSystems.Truth
