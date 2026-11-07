module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.rePred
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.regularLanguage
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodIso

public import Mathlib.Computability.Primrec.Basic

public import Mathlib.Data.Nat.Bitwise

import Mathlib.Tactic.Ring

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace RegularLanguage
open scoped Computability
open Sum Set
section
variable {σ₁ σ₂ : Type}
variable {σ : Type}

theorem consistentB_iff_Ssys (a b : SExpr) (ha : InS (denote a)) (hb : InS (denote b)) :
    consistentB a b = true ↔ InS (denote a ∩ denote b) := by
  rw [← denote_cap, consistentB_iff]
  exact Iff.symm (Ssys_isPositive (Ssys_mem.mpr ha) (Ssys_mem.mpr hb))
end

end RegularLanguage
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.RegularLanguage
set_option linter.unusedVariables false

theorem example_722_decide : ∀ (a b : DomainTheory.NeighbourhoodSystems.RegularLanguage.SExpr),
  DomainTheory.NeighbourhoodSystems.RegularLanguage.InS (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote a) →
    DomainTheory.NeighbourhoodSystems.RegularLanguage.InS (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote b) →
      Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.RegularLanguage.consistentB a b) Bool.true)
        (DomainTheory.NeighbourhoodSystems.RegularLanguage.InS
          (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool))
            (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote a)
            (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote b))) :=
  DomainTheory.NeighbourhoodSystems.RegularLanguage.consistentB_iff_Ssys

end DomainTheory.NeighbourhoodSystems.RegularLanguage
namespace DomainTheory.NeighbourhoodSystems
namespace RegularLanguage
open scoped Computability
open Sum Set

section
variable {σ₁ σ₂ : Type}
variable {σ : Type}

theorem denote_eq_empty_iff (e : SExpr) :
    denote e = ∅ ↔ ∀ s ∈ (toNFA e).accept, ∀ x, s ∉ (toNFA e).eval x := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s hs x hse
    exact h x (by rw [← toNFA_accepts e]; exact ⟨s, hs, hse⟩)
  · intro h x hx
    rw [← toNFA_accepts e] at hx
    obtain ⟨s, hs, hse⟩ := hx
    exact h s hs x hse

theorem nfa_accepts_nonempty_iff (M : NFA Bool σ) :
    M.accepts.Nonempty ↔ ∃ s ∈ M.accept, ∃ x, s ∈ M.eval x := by
  constructor
  · rintro ⟨x, S, hS, hSe⟩; exact ⟨S, hS, x, hSe⟩
  · rintro ⟨S, hS, x, hSe⟩; exact ⟨x, S, hS, hSe⟩

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts := by
  constructor
  · intro h
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short h
    refine ⟨w, ?_, hw⟩
    rw [mem_wordsUpTo]
    omega
  · intro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

omit [Fintype σ] in
theorem pathStateAt_last {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p x.length (Nat.le_refl _) = t := by
  induction p with
  | nil s => simp [pathStateAt, pathStateAtAux]
  | cons sMid s' u a xs hstep p' ih =>
    simp [pathStateAt, pathStateAtAux, List.length_cons]
    exact ih

end ShortWord

end

def acceptFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)}
  | .cap a b => (acceptFin a) ×ˢ (acceptFin b)
  | .cat a b => (acceptFin b).image (inr : autState b → autState a ⊕ autState b)

def startFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)}
  | .cap a b => (startFin a) ×ˢ (startFin b)
  | .cat a b =>
      if ((startFin a) ∩ (acceptFin a)).Nonempty
      then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
        (startFin b).image (inr : autState b → autState a ⊕ autState b)
      else (startFin a).image (inl : autState a → autState a ⊕ autState b)

def stepFinSingle : (e : SExpr) → autState e → Bool → Finset (autState e)
  | .sigma => fun _ _ => Finset.univ
  | .single σ => fun s c => {(singleDFA σ).step s c}
  | .cap a b => fun s c => (stepFinSingle a s.1 c) ×ˢ (stepFinSingle b s.2 c)
  | .cat a b => fun s c =>
      match s with
      | inl s' =>
          if ((stepFinSingle a s' c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b)
      | inr s' => (stepFinSingle b s' c).image (inr : autState b → autState a ⊕ autState b)

def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)

def diffNFA (e1 e2 : SExpr) : NFA Bool (Finset (autState e1) × Finset (autState e2)) where
  step S c := {(stepFin e1 S.1 c, stepFin e2 S.2 c)}
  start := {(startFin e1, startFin e2)}
  accept := {S | (S.1 ∩ acceptFin e1).Nonempty ∧ S.2 ∩ acceptFin e2 = ∅}

def evalFin (e : SExpr) (w : List Bool) : Finset (autState e) :=
  w.foldl (stepFin e) (startFin e)

def subsetB (e1 e2 : SExpr) : Bool :=
  (wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2)))).all
    (fun w => !matchesB e1 w || matchesB e2 w)

def interEqB (e1 e2 : SExpr) : Bool := subsetB e1 e2 && subsetB e2 e1

theorem coe_acceptFin : ∀ e : SExpr, (↑(acceptFin e) : Set (autState e)) = (toNFA e).accept
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.accept
      show (↑(Finset.univ : Finset Unit) : Set Unit) = Set.univ
      ext x; cases x; simp
  | .single σ => by
      change (↑({(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)} : Finset _) : Set _)
        = (singleDFA σ).toNFA.accept
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      change (↑((acceptFin a) ×ˢ (acceptFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).accept
      rw [Finset.coe_product, coe_acceptFin a, coe_acceptFin b]
      rfl
  | .cat a b => by
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.accept
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = inr '' (toNFA b).accept
      rw [Finset.coe_image, coe_acceptFin b]

theorem coe_startFin : ∀ e : SExpr, (↑(startFin e) : Set (autState e)) = (toNFA e).start
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.start
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.start}
      ext x; cases x; simp
  | .single σ => by
      show (↑({(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.start
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      show (↑((startFin a) ×ˢ (startFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).start
      rw [Finset.coe_product, coe_startFin a, coe_startFin b]
      rfl
  | .cat a b => by
      show (↑(if ((startFin a) ∩ (acceptFin a)).Nonempty
          then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (startFin a).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.start
      show _ = (catEps (toNFA a) (toNFA b)).εClosure (catEps (toNFA a) (toNFA b)).start
      rw [catEps_start]
      by_cases hne : ((startFin a) ∩ (acceptFin a)).Nonempty
      · rw [ite_eq_left hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
        simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
        constructor
        · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · refine Or.inr ⟨?_, q, hq, rfl⟩
            obtain ⟨q0, hq0⟩ := hne
            rw [Finset.mem_inter] at hq0
            exact ⟨q0, hq0.2, q0, hq0.1, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · exact Or.inr ⟨q, hq, rfl⟩
      · rw [ite_eq_right hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne

theorem coe_stepFinSingle : ∀ (e : SExpr) (s : autState e) (c : Bool),
    (↑(stepFinSingle e s c) : Set (autState e)) = (toNFA e).step s c
  | .sigma, s, c => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.step s c
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.step s c}
      ext x; cases x; simp
  | .single σ, s, c => by
      show (↑({(singleDFA σ).step s c} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.step s c
      simp [DFA.toNFA]
  | .cap a b, (s1, s2), c => by
      show (↑((stepFinSingle a s1 c) ×ˢ (stepFinSingle b s2 c)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).step (s1, s2) c
      rw [Finset.coe_product, coe_stepFinSingle a s1 c, coe_stepFinSingle b s2 c]
      rfl
  | .cat a b, inl s, c => by
      show (↑(if ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inl s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inl s) (some c))
      rw [catEps_step_inl_some]
      by_cases hne : ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
      · rw [ite_eq_left hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
        constructor
        · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · refine Or.inr ⟨?_, q, hq, rfl⟩
            obtain ⟨q0, hq0⟩ := hne
            rw [Finset.mem_inter] at hq0
            exact ⟨q0, hq0.2, q0, hq0.1, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · exact Or.inr ⟨q, hq, rfl⟩
      · rw [ite_eq_right hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne
  | .cat a b, inr s, c => by
      show (↑((stepFinSingle b s c).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inr s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inr s) (some c))
      rw [catEps_step_inr_some]
      ext x
      rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle b s c]
      simp only [Finset.coe_image, mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
      · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, _, hqmem⟩, _⟩)
        · exact ⟨q, hq, rfl⟩
        · exact absurd hqmem (by simp)

theorem coe_stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) :
    (↑(stepFin e S c) : Set (autState e)) = (toNFA e).stepSet ↑S c := by
  ext x
  rw [Finset.mem_coe]
  unfold stepFin
  rw [Finset.mem_biUnion, NFA.mem_stepSet]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c]; exact Finset.mem_coe.mpr hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c] at hx; exact Finset.mem_coe.mp hx⟩

theorem coe_foldl_stepFin (e : SExpr) (w : List Bool) (S : Finset (autState e)) :
    (↑(w.foldl (stepFin e) S) : Set (autState e)) = (toNFA e).evalFrom ↑S w := by
  induction w generalizing S with
  | nil => rfl
  | cons c w ih =>
    show (↑(w.foldl (stepFin e) (stepFin e S c)) : Set (autState e)) = _
    rw [ih (stepFin e S c), NFA.evalFrom_cons, coe_stepFin e S c]

theorem coe_evalFin (e : SExpr) (w : List Bool) :
    (↑(evalFin e w) : Set (autState e)) = (toNFA e).eval w := by
  show (↑(w.foldl (stepFin e) (startFin e)) : Set (autState e))
    = (toNFA e).evalFrom (toNFA e).start w
  rw [coe_foldl_stepFin e w (startFin e), coe_startFin e]

theorem denote_iff_evalFin (e : SExpr) (w : List Bool) :
    w ∈ denote e ↔ (evalFin e w ∩ acceptFin e).Nonempty := by
  rw [← toNFA_accepts e]
  constructor
  · rintro ⟨s, hs, hse⟩
    refine ⟨s, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← Finset.mem_coe, coe_evalFin]; exact hse
    · rw [← Finset.mem_coe, coe_acceptFin]; exact hs
  · rintro ⟨s, hs⟩
    rw [Finset.mem_inter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨s, ?_, ?_⟩
    · rw [← Finset.mem_coe, coe_acceptFin] at hs2; exact hs2
    · rw [← Finset.mem_coe, coe_evalFin] at hs1; exact hs1

theorem diffNFA_evalFrom (e1 e2 : SExpr) (w : List Bool)
    (S1 : Finset (autState e1)) (S2 : Finset (autState e2)) :
    (diffNFA e1 e2).evalFrom {(S1, S2)} w =
      {(w.foldl (stepFin e1) S1, w.foldl (stepFin e2) S2)} := by
  induction w generalizing S1 S2 with
  | nil => rfl
  | cons c w ih =>
    show (diffNFA e1 e2).evalFrom ((diffNFA e1 e2).stepSet {(S1, S2)} c) w = _
    rw [NFA.stepSet_singleton]
    show (diffNFA e1 e2).evalFrom {(stepFin e1 S1 c, stepFin e2 S2 c)} w = _
    exact ih (stepFin e1 S1 c) (stepFin e2 S2 c)

theorem diffNFA_eval (e1 e2 : SExpr) (w : List Bool) :
    (diffNFA e1 e2).eval w = {(evalFin e1 w, evalFin e2 w)} := by
  show (diffNFA e1 e2).evalFrom (diffNFA e1 e2).start w = _
  show (diffNFA e1 e2).evalFrom {(startFin e1, startFin e2)} w = _
  exact diffNFA_evalFrom e1 e2 w (startFin e1) (startFin e2)

theorem diffNFA_mem_accepts_iff (e1 e2 : SExpr) (w : List Bool) :
    w ∈ (diffNFA e1 e2).accepts ↔ w ∈ denote e1 ∧ w ∉ denote e2 := by
  constructor
  · rintro ⟨s, hs, hse⟩
    rw [diffNFA_eval, Set.mem_singleton_iff] at hse
    subst hse
    obtain ⟨hacc1, hacc2⟩ := hs
    refine ⟨(denote_iff_evalFin e1 w).mpr hacc1, fun hmem => ?_⟩
    rw [denote_iff_evalFin] at hmem
    rw [hacc2] at hmem
    exact Finset.not_nonempty_empty hmem
  · rintro ⟨h1, h2⟩
    refine ⟨(evalFin e1 w, evalFin e2 w), ⟨(denote_iff_evalFin e1 w).mp h1, ?_⟩, ?_⟩
    · show evalFin e2 w ∩ acceptFin e2 = ∅
      by_contra hcontra
      exact h2 ((denote_iff_evalFin e2 w).mpr (Finset.nonempty_iff_ne_empty.mpr hcontra))
    · rw [diffNFA_eval]; rfl

theorem exists_diff_word_short {e1 e2 : SExpr} (h : ¬ denote e1 ⊆ denote e2) :
    ∃ w, w.length < Fintype.card (Finset (autState e1) × Finset (autState e2)) ∧
      w ∈ denote e1 ∧ w ∉ denote e2 := by
  rw [Set.not_subset] at h
  have hne : (diffNFA e1 e2).accepts.Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := h
    exact ⟨x, (diffNFA_mem_accepts_iff e1 e2 x).mpr ⟨hx1, hx2⟩⟩
  obtain ⟨w, hlen, hmem⟩ := exists_accepted_word_short hne
  exact ⟨w, hlen, (diffNFA_mem_accepts_iff e1 e2 w).mp hmem⟩

theorem subsetB_iff (e1 e2 : SExpr) : subsetB e1 e2 = true ↔ denote e1 ⊆ denote e2 := by
  unfold subsetB
  rw [List.all_eq_true]
  constructor
  · intro h
    by_contra hsub
    obtain ⟨w, hlen, hw1, hw2⟩ := exists_diff_word_short hsub
    have hwmem : w ∈ wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2))) :=
      (mem_wordsUpTo _).mpr (le_of_lt hlen)
    have hor := h w hwmem
    have he1 : matchesB e1 w = true := (matchesB_iff e1 w).mpr hw1
    rw [he1] at hor
    simp only [Bool.not_true, Bool.false_or] at hor
    exact hw2 ((matchesB_iff e2 w).mp hor)
  · intro hsub w _
    by_cases hw1 : w ∈ denote e1
    · have he2 : matchesB e2 w = true := (matchesB_iff e2 w).mpr (hsub hw1)
      simp [he2]
    · have he1 : matchesB e1 w = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact hw1 ((matchesB_iff e1 w).mp hc)
      simp [he1]

theorem interEqB_iff (e1 e2 : SExpr) : interEqB e1 e2 = true ↔ denote e1 = denote e2 := by
  unfold interEqB
  rw [Bool.and_eq_true, subsetB_iff, subsetB_iff, ← Set.Subset.antisymm_iff]

end RegularLanguage
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.RegularLanguage
set_option linter.unusedVariables false

theorem example_722_equiv : ∀ (e1 e2 : DomainTheory.NeighbourhoodSystems.RegularLanguage.SExpr),
  Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.RegularLanguage.interEqB e1 e2) Bool.true)
    (@Eq (Set (List Bool)) (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote e1)
      (DomainTheory.NeighbourhoodSystems.RegularLanguage.denote e2)) :=
  DomainTheory.NeighbourhoodSystems.RegularLanguage.interEqB_iff

end DomainTheory.NeighbourhoodSystems.RegularLanguage

namespace Domain.Recursive
open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def autStateCardFuelCharBody (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  let subAdd := prev c.unpair.2.unpair.1 + prev c.unpair.2.unpair.2
  let subMul := prev c.unpair.2.unpair.1 * prev c.unpair.2.unpair.2
  selectFn (isOne (1 - c.unpair.1))
    1
    (selectFn (isOne (2 - c.unpair.1))
      (listLenChar c.unpair.2 + 2)
      (selectFn (isOne (3 - c.unpair.1))
        subAdd
        (selectFn (isOne (4 - c.unpair.1)) subMul 0)))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def autStateCardFuelChar : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => autStateCardFuelCharBody (autStateCardFuelChar fuel) c

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def c9b5_boolNat (b : Bool) : ℕ := if b then 1 else 0

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def c9b5_encodeListBool (σ : List Bool) : ℕ := encodeList (σ.map c9b5_boolNat)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def c9b5_sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)
  | .cap a b => 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def c9b5_sexprGodelEncode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (c9b5_encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))
  | .cap a b => Nat.pair 3 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def capCode (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def autStateCardFuelCharLookup (w : ℕ) : ℕ :=
  autStateCardFuelCharBody (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def subsetBoundChar (fuel c1 c2 : ℕ) : ℕ :=
  2 ^ (autStateCardFuelChar fuel c1) * 2 ^ (autStateCardFuelChar fuel c2)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def subsetGuardChar (fuel c1 c2 i : ℕ) : ℕ :=
  mulBit (allBinDigitsChar i) (isOne (1 - (listLenChar i - subsetBoundChar fuel c1 c2)))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def matchesBCatG (prev : ℕ → ℕ) (p : ℕ) : ℕ :=
  let i := p.unpair.1
  let c := p.unpair.2.unpair.1
  let cw := p.unpair.2.unpair.2
  mulBit (prev (Nat.pair c.unpair.2.unpair.1 (takeCode i cw)))
        (prev (Nat.pair c.unpair.2.unpair.2 (dropCode i cw)))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def matchesBCatGLookup (w : ℕ) : ℕ :=
  matchesBCatG (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def matchesBCharBody (prev : ℕ → ℕ) (c cw : ℕ) : ℕ :=
  let catExist := bExistsFn (matchesBCatG prev) (Nat.pair c cw) (listLenChar cw + 1)
  let capAnd := mulBit (prev (Nat.pair c.unpair.2.unpair.1 cw))
                    (prev (Nat.pair c.unpair.2.unpair.2 cw))
  selectFn (isOne (1 - c.unpair.1))
    1
    (selectFn (isOne (2 - c.unpair.1))
      (listEqChar cw c.unpair.2)
      (selectFn (isOne (3 - c.unpair.1))
        catExist
        (selectFn (isOne (4 - c.unpair.1)) capAnd 0)))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

def matchesBChar : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, c, cw =>
      matchesBCharBody (fun p => matchesBChar fuel p.unpair.1 p.unpair.2) c cw

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def decideNonemptyBChar (fuel : ℕ) (c_e : ℕ) : ℕ :=
  bExistsFn (fun p =>
      mulBit (allBinDigitsChar p.unpair.1) (matchesBChar fuel p.unpair.2 p.unpair.1))
    c_e (codeBound (autStateCardFuelChar fuel c_e))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def consistentBChar (fuel : ℕ) (c1 c2 : ℕ) : ℕ :=
  decideNonemptyBChar fuel (capCode c1 c2)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def matchesBCharBodyLookup (w : ℕ) : ℕ :=
  matchesBCharBody (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2.unpair.1 w.unpair.2.unpair.2

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

@[irreducible] def subsetBChar (fuel c1 c2 : ℕ) : ℕ :=
  bForallFn (fun p =>
      selectFn (subsetGuardChar fuel p.unpair.2.unpair.1 p.unpair.2.unpair.2 p.unpair.1)
        (selectFn (matchesBChar fuel p.unpair.2.unpair.1 p.unpair.1)
          (matchesBChar fuel p.unpair.2.unpair.2 p.unpair.1) 1)
        1)
    (Nat.pair c1 c2) (codeBound (subsetBoundChar fuel c1 c2))

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

@[irreducible] def interEqChar (fuel c1 c2 : ℕ) : ℕ :=
  mulBit (subsetBChar fuel c1 c2) (subsetBChar fuel c2 c1)

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems RegularLanguage
open DomainTheory.NeighbourhoodSystems.RegularLanguage

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def c9b6_decodeListBool (c : ℕ) : List Bool :=
  (decodeList c).map fun n => decide (n = 1)

private theorem c9b5_decodeList_encodeListBool (σ : List Bool) :
    decodeList (c9b5_encodeListBool σ) = σ.map c9b5_boolNat := by
  simp [c9b5_encodeListBool, decodeList_encodeList]

private theorem c9b5_boolNat_injective : Function.Injective c9b5_boolNat := by
  intro b c h
  cases b <;> cases c <;> first | rfl | simp [c9b5_boolNat] at h

private theorem c9b5_decodeList_injective {c1 c2 : ℕ} (h : decodeList c1 = decodeList c2) : c1 = c2 := by
  have := congrArg encodeList h
  rwa [encodeList_decodeList, encodeList_decodeList] at this

private theorem c9b5_map_boolNat_eq_iff (w σ : List Bool) :
    w.map c9b5_boolNat = σ.map c9b5_boolNat ↔ w = σ := by
  constructor
  · intro h
    revert σ
    induction w with
    | nil =>
      intro σ h
      cases σ with
      | nil => rfl
      | cons _ _ => simp at h
    | cons b w ih =>
      intro σ h
      cases σ with
      | nil => simp at h
      | cons c σ =>
        simp only [List.map_cons] at h
        obtain ⟨hb, ht⟩ := List.cons.inj h
        have hb' : b = c := by
          cases b <;> cases c <;> first | rfl | simp [c9b5_boolNat] at hb
        exact hb' ▸ congrArg (List.cons c) (ih σ ht)
  · intro h; rw [h]

private theorem c9b5_takeCode_encodeListBool (w : List Bool) (i : ℕ) :
    takeCode i (c9b5_encodeListBool w) = c9b5_encodeListBool (w.take i) := by
  apply c9b5_decodeList_injective
  rw [takeCode_eq, c9b5_decodeList_encodeListBool, ← List.map_take]
  rw [c9b5_decodeList_encodeListBool (σ := w.take i)]

private theorem c9b5_dropCode_encodeListBool (w : List Bool) (i : ℕ) :
    dropCode i (c9b5_encodeListBool w) = c9b5_encodeListBool (w.drop i) := by
  apply c9b5_decodeList_injective
  rw [dropCode_eq, c9b5_decodeList_encodeListBool, ← List.map_drop]
  rw [c9b5_decodeList_encodeListBool (σ := w.drop i)]

private theorem c9b5_listEqChar_encodeListBool (w σ : List Bool) :
    listEqChar (c9b5_encodeListBool w) (c9b5_encodeListBool σ) = 1 ↔ w = σ := by
  simp only [listEqChar_eq_one_iff, c9b5_decodeList_encodeListBool, c9b5_map_boolNat_eq_iff]

theorem autStateCardFuelCharBody_eq (prev : ℕ → ℕ) (c : ℕ) :
    autStateCardFuelCharBody prev c =
      match c.unpair.1 with
      | 0 => 1
      | 1 => listLenChar c.unpair.2 + 2
      | 2 => prev c.unpair.2.unpair.1 + prev c.unpair.2.unpair.2
      | 3 => prev c.unpair.2.unpair.1 * prev c.unpair.2.unpair.2
      | _ => 0 := by
  unfold autStateCardFuelCharBody
  match tag : c.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01 : (1 - 1 : ℕ) = 0 := rfl
    have h12 : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01, h12, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01 : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 2 : ℕ) = 0 := rfl
    have h23 : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01, h23, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01 : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23 : (3 - 3 : ℕ) = 0 := rfl
    have h34 : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01, h34, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have hne1 : isOne (1 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne2 : isOne (2 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne3 : isOne (3 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne4 : isOne (4 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    simp only [hne1, hne2, hne3, hne4, selectFn_zero]

theorem autStateCardFuelChar_eq_autStateCard {fuel : ℕ} {e : SExpr}
    (h : c9b5_sexprDepth e ≤ fuel) :
    autStateCardFuelChar fuel (c9b5_sexprGodelEncode e) = autStateCard e := by
  induction e generalizing fuel with
  | sigma =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard]
  | single σ =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        listLenChar_eq, c9b5_decodeList_encodeListBool, List.length_map]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        iha ha, ihb hb]
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      simp [autStateCardFuelChar, autStateCardFuelCharBody_eq, c9b5_sexprGodelEncode, autStateCard,
        iha ha, ihb hb]

theorem primrec_autStateCardFuelCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun c => autStateCardFuelCharBody prev c) := by
  unfold autStateCardFuelCharBody
  have hleft : Nat.Primrec (fun c => prev c.unpair.2.unpair.1) :=
    (hprev.comp (Nat.Primrec.left.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hright : Nat.Primrec (fun c => prev c.unpair.2.unpair.2) :=
    (hprev.comp (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hadd := primrec_add₂ hleft hright
  have hmul := primrec_mul₂ hleft hright
  have hf1 := primrec_add₂ (primrec_listLenChar.comp Nat.Primrec.right) (Nat.Primrec.const 2)
  exact primrec_tagCase4 (Nat.Primrec.const 1) hf1 hadd hmul (Nat.Primrec.const 0)

theorem autStateCardFuelCharBody_local (f g : ℕ → ℕ) (c : ℕ) (h : ∀ c' ≤ c, f c' = g c') :
    autStateCardFuelCharBody f c = autStateCardFuelCharBody g c := by
  rw [autStateCardFuelCharBody_eq, autStateCardFuelCharBody_eq]
  have h1 : c.unpair.2.unpair.1 ≤ c := le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)
  have h2 : c.unpair.2.unpair.2 ≤ c := le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)
  rw [h _ h1, h _ h2]

theorem matchesBCharBody_eq (prev : ℕ → ℕ) (c cw : ℕ) :
    matchesBCharBody prev c cw =
      match c.unpair.1 with
      | 0 => 1
      | 1 => listEqChar cw c.unpair.2
      | 2 =>
        bExistsFn (matchesBCatG prev) (Nat.pair c cw) (listLenChar cw + 1)
      | 3 =>
        mulBit (prev (Nat.pair c.unpair.2.unpair.1 cw))
              (prev (Nat.pair c.unpair.2.unpair.2 cw))
      | _ => 0 := by
  unfold matchesBCharBody matchesBCatG
  match tag : c.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01 : (1 - 1 : ℕ) = 0 := rfl
    have h12 : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01, h12, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01 : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 2 : ℕ) = 0 := rfl
    have h23 : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01, h23, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01 : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12 : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23 : (3 - 3 : ℕ) = 0 := rfl
    have h34 : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01, h34, isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have hne1 : isOne (1 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne2 : isOne (2 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne3 : isOne (3 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    have hne4 : isOne (4 - (t + 4)) = 0 := isOne_of_ne_one (by omega)
    simp only [hne1, hne2, hne3, hne4, selectFn_zero]

private theorem c9b5_matchesBCatG_char (fuel : ℕ) (a b : SExpr) (w : List Bool) (i : ℕ) :
    matchesBCatG (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
        (Nat.pair i
          (Nat.pair (Nat.pair 2 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b)))
            (c9b5_encodeListBool w))) =
      mulBit (matchesBChar fuel (c9b5_sexprGodelEncode a) (takeCode i (c9b5_encodeListBool w)))
        (matchesBChar fuel (c9b5_sexprGodelEncode b) (dropCode i (c9b5_encodeListBool w))) := by
  simp [matchesBCatG]

set_option maxHeartbeats 1600000 in
theorem matchesBChar_eq_one_iff {fuel : ℕ} {e : SExpr} {w : List Bool}
    (h : c9b5_sexprDepth e ≤ fuel) :
    matchesBChar fuel (c9b5_sexprGodelEncode e) (c9b5_encodeListBool w) = 1 ↔
      matchesB e w = true := by
  induction e generalizing fuel w with
  | sigma =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel => simp [matchesBChar, matchesBCharBody_eq, matchesB, c9b5_sexprGodelEncode]
  | single σ =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      simp [matchesBChar, matchesBCharBody_eq, c9b5_sexprGodelEncode, matchesB,
        c9b5_listEqChar_encodeListBool w σ, decide_eq_true_eq]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hbody := matchesBCharBody_eq (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
          (c9b5_sexprGodelEncode (.cat a b)) (c9b5_encodeListBool w)
      rw [matchesBChar, hbody]
      simp only [c9b5_sexprGodelEncode, unpair_pair_fst, matchesB, List.any_eq_true]
      rw [bExistsFn_eq_one_iff]
      have hlen : listLenChar (c9b5_encodeListBool w) + 1 = w.length + 1 := by
        simp [listLenChar_eq, c9b5_decodeList_encodeListBool, List.length_map]
      constructor
      · intro ⟨i, hi, hg⟩
        rw [c9b5_matchesBCatG_char, mulBit_eq_one_iff] at hg
        obtain ⟨h1, h2⟩ := hg
        have hi' : i < w.length + 1 := by rw [← hlen]; exact hi
        refine ⟨i, (List.mem_range).2 hi', ?_⟩
        simp only [Bool.and_eq_true]
        exact ⟨(iha ha).mp (by rw [← c9b5_takeCode_encodeListBool w i]; exact h1),
          (ihb hb).mp (by rw [← c9b5_dropCode_encodeListBool w i]; exact h2)⟩
      · intro ⟨i, hi, hfg⟩
        have hi' : i < listLenChar (c9b5_encodeListBool w) + 1 := by
          rw [hlen]; exact (List.mem_range).1 hi
        refine ⟨i, hi', ?_⟩
        rw [c9b5_matchesBCatG_char, mulBit_eq_one_iff]
        simp [Bool.and_eq_true] at hfg
        refine And.intro ?h1 ?h2
        · simpa [c9b5_takeCode_encodeListBool w i] using (iha ha).mpr hfg.1
        · simpa [c9b5_dropCode_encodeListBool w i] using (ihb hb).mpr hfg.2
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [c9b5_sexprDepth] at h
    | succ fuel =>
      have ha : c9b5_sexprDepth a ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hb : c9b5_sexprDepth b ≤ fuel := by
        simp only [c9b5_sexprDepth] at h ⊢; omega
      have hbody := matchesBCharBody_eq (fun p => matchesBChar fuel p.unpair.1 p.unpair.2)
          (c9b5_sexprGodelEncode (.cap a b)) (c9b5_encodeListBool w)
      rw [matchesBChar, hbody]
      simp only [c9b5_sexprGodelEncode, unpair_pair_fst, unpair_pair_snd, matchesB, mulBit_eq_one_iff]
      constructor
      · intro ⟨h1, h2⟩
        rw [Bool.and_eq_true]
        exact ⟨(iha ha).mp h1, (ihb hb).mp h2⟩
      · intro hfg
        rw [Bool.and_eq_true] at hfg
        exact ⟨(iha ha).mpr hfg.1, (ihb hb).mpr hfg.2⟩

set_option maxHeartbeats 800000 in
private theorem primrec_matchesBCatG {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun p => matchesBCatG prev p) := by
  have hc := Nat.Primrec.left.comp Nat.Primrec.right
  have ha := Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb := Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hcw := Nat.Primrec.right.comp Nat.Primrec.right
  have hi := Nat.Primrec.left
  have h1 := hprev.comp (Nat.Primrec.pair ha (primrec_takeCode.comp (hi.pair hcw)))
  have h2 := hprev.comp (Nat.Primrec.pair hb (primrec_dropCode.comp (hi.pair hcw)))
  exact (primrec_mul₂ h1 h2).of_eq fun p => by
    dsimp [matchesBCatG, mulBit]
    simp only [unpair_pair_fst, unpair_pair_snd]

set_option maxHeartbeats 800000 in
theorem primrec_matchesBCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun t => matchesBCharBody prev t.unpair.1 t.unpair.2) := by
  have htag : Nat.Primrec (fun t => (t.unpair.1).unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  have h23 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) htag)
  have h34 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) htag)
  have hf1 := primrec_listEqChar.comp (Nat.Primrec.pair Nat.Primrec.right
    (Nat.Primrec.right.comp Nat.Primrec.left))
  have hpack : Nat.Primrec (fun t => Nat.pair t (listLenChar t.unpair.2 + 1)) :=
    Nat.Primrec.pair primrec_id
      (primrec_add₂ (primrec_listLenChar.comp Nat.Primrec.right) (Nat.Primrec.const 1))
  have hcat := (primrec_bExistsFn (primrec_matchesBCatG hprev)).comp hpack
  have hc := Nat.Primrec.left
  have ha := Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb := Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hcw := Nat.Primrec.right
  have hcap := primrec_mulBit.comp (Nat.Primrec.pair
    (hprev.comp (Nat.Primrec.pair ha hcw)) (hprev.comp (Nat.Primrec.pair hb hcw)))
  exact (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hcat
        (primrec_selectFn h34 hcap (Nat.Primrec.const 0))))).of_eq fun t => by
    rw [matchesBCharBody_eq]
    match tag : (t.unpair.1).unpair.1 with
    | 0 | 1 | 2 | 3 =>
      simp [selectFn, isOne, mulBit]
    | _ + 4 =>
      simp [selectFn, isOne, mulBit]

theorem matchesBChar_le_one : ∀ fuel c cw, matchesBChar fuel c cw ≤ 1
  | 0, _, _ => by simp [matchesBChar]
  | fuel + 1, c, cw => by
    rw [matchesBChar, matchesBCharBody_eq]
    match tag : c.unpair.1 with
    | 0 => simp
    | 1 => exact listEqChar_le_one _ _
    | 2 => exact bExistsFn_le_one _ _ _
    | 3 =>
      exact mulBit_le_one (matchesBChar_le_one fuel _ _) (matchesBChar_le_one fuel _ _)
    | _ + 4 => simp

theorem matchesBCharBody_local (f g : ℕ → ℕ) (c cw : ℕ)
    (h : ∀ p ≤ Nat.pair c cw, f p = g p) : matchesBCharBody f c cw = matchesBCharBody g c cw := by
  rw [matchesBCharBody_eq, matchesBCharBody_eq]
  match tag : c.unpair.1 with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    simp
    apply bExistsFn_congr
    intro i _
    unfold matchesBCatG
    simp only [unpair_pair_fst, unpair_pair_snd]
    have h1 : Nat.pair c.unpair.2.unpair.1 (takeCode i cw) ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)) (takeCode_le i cw)
    have h2 : Nat.pair c.unpair.2.unpair.2 (dropCode i cw) ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)) (dropCode_le i cw)
    rw [h _ h1, h _ h2]
  | 3 =>
    simp
    have h1 : Nat.pair c.unpair.2.unpair.1 cw ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)) (le_refl cw)
    have h2 : Nat.pair c.unpair.2.unpair.2 cw ≤ Nat.pair c cw :=
      pair_le_pair (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)) (le_refl cw)
    rw [h _ h1, h _ h2]
  | _ + 4 => rfl

private theorem c9b6_allBinDigitsChar_encodeListBool (w : List Bool) :
    allBinDigitsChar (c9b5_encodeListBool w) = 1 := by
  rw [allBinDigitsChar_eq_one_iff]
  intro x hx
  rw [c9b5_decodeList_encodeListBool] at hx
  simp only [List.mem_map] at hx
  obtain ⟨b, _, hb⟩ := hx
  cases b <;> simp [c9b5_boolNat] at hb <;> omega

private theorem c9b6_encodeListBool_lt_codeBound {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    c9b5_encodeListBool w < codeBound n := by
  apply codeBound_ge n (c9b5_encodeListBool w)
  · rw [c9b5_decodeList_encodeListBool, List.length_map]; exact hw
  · intro x hx
    rw [c9b5_decodeList_encodeListBool] at hx
    simp only [List.mem_map] at hx
    obtain ⟨b, _, hb⟩ := hx
    cases b <;> simp [c9b5_boolNat] at hb <;> omega

private theorem c9b6_boolNat_decide_eq (x : ℕ) (hx : x = 0 ∨ x = 1) :
    c9b5_boolNat (decide (x = 1)) = x := by
  rcases hx with rfl | rfl <;> simp [c9b5_boolNat]

private theorem c9b6_encodeListBool_decodeListBool_of_allBin {c : ℕ}
    (hall : allBinDigitsChar c = 1) :
    c9b5_encodeListBool (c9b6_decodeListBool c) = c := by
  rw [allBinDigitsChar_eq_one_iff] at hall
  apply c9b5_decodeList_injective
  rw [c9b5_decodeList_encodeListBool, c9b6_decodeListBool, List.map_map]
  conv_rhs => rw [← List.map_id (decodeList c)]
  exact List.map_congr_left (fun x hx => c9b6_boolNat_decide_eq x (hall x hx))

private theorem c9b6_matchesBChar_of_allBin {fuel : ℕ} {e : SExpr} {c : ℕ}
    (h : c9b5_sexprDepth e ≤ fuel) (hall : allBinDigitsChar c = 1)
    (hmatch : matchesBChar fuel (c9b5_sexprGodelEncode e) c = 1) :
    matchesB e (c9b6_decodeListBool c) = true := by
  apply (matchesBChar_eq_one_iff (w := c9b6_decodeListBool c) h).1
  rwa [c9b6_encodeListBool_decodeListBool_of_allBin hall]

theorem decideNonemptyBChar_eq_one_iff {fuel : ℕ} {e : SExpr}
    (h : c9b5_sexprDepth e ≤ fuel) :
    decideNonemptyBChar fuel (c9b5_sexprGodelEncode e) = 1 ↔ (denote e).Nonempty := by
  simp only [decideNonemptyBChar, bExistsFn_eq_one_iff, unpair_pair_fst, unpair_pair_snd,
    mulBit_eq_one_iff]
  constructor
  · rintro ⟨i, -, hall, hmatch⟩
    exact ⟨c9b6_decodeListBool i, (matchesB_iff e _).mp (c9b6_matchesBChar_of_allBin h hall hmatch)⟩
  · intro hne
    obtain ⟨w, hwmem, hmatch⟩ := (denote_nonempty_iff_short e).mp hne
    refine ⟨c9b5_encodeListBool w, ?_, c9b6_allBinDigitsChar_encodeListBool w,
      (matchesBChar_eq_one_iff h).2 hmatch⟩
    rw [autStateCardFuelChar_eq_autStateCard h]
    exact c9b6_encodeListBool_lt_codeBound (by rwa [mem_wordsUpTo] at hwmem)

theorem c9b6_sexprGodelEncode_cap (a b : SExpr) :
    c9b5_sexprGodelEncode (.cap a b) = capCode (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b) :=
  rfl

theorem subsetGuardChar_le_one (fuel c1 c2 i : ℕ) : subsetGuardChar fuel c1 c2 i ≤ 1 :=
  mulBit_le_one (allBinDigitsChar_le_one _) (isOne_le_one _)

set_option maxHeartbeats 800000 in
theorem subsetBChar_eq_one_iff {fuel : ℕ} {e1 e2 : SExpr}
    (h1 : c9b5_sexprDepth e1 ≤ fuel) (h2 : c9b5_sexprDepth e2 ≤ fuel) :
    subsetBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) = 1 ↔
      denote e1 ⊆ denote e2 := by
  rw [← subsetB_iff]
  have hbound : subsetBoundChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) =
      Fintype.card (Finset (autState e1) × Finset (autState e2)) := by
    unfold subsetBoundChar
    rw [autStateCardFuelChar_eq_autStateCard h1, autStateCardFuelChar_eq_autStateCard h2,
      autStateCard_eq_card, autStateCard_eq_card, Fintype.card_prod, Fintype.card_finset,
      Fintype.card_finset]
  unfold subsetB subsetBChar
  rw [List.all_eq_true, bForallFn_eq_one_iff]
  simp only [unpair_pair_fst, unpair_pair_snd, hbound]
  constructor
  · intro h w hwmem
    rw [mem_wordsUpTo] at hwmem
    have hi := h (c9b5_encodeListBool w) (c9b6_encodeListBool_lt_codeBound hwmem)
    have hguard1 : subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2)
        (c9b5_encodeListBool w) = 1 := by
      unfold subsetGuardChar
      rw [c9b6_allBinDigitsChar_encodeListBool, mulBit, one_mul, listLenChar_eq,
        c9b5_decodeList_encodeListBool, List.length_map, hbound,
        Nat.sub_eq_zero_of_le hwmem]
      exact isOne_one
    rw [hguard1, selectFn_one] at hi
    by_cases hc1 : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w) = 1
    · rw [hc1, selectFn_one] at hi
      simp only [Bool.or_eq_true]
      exact Or.inr ((matchesBChar_eq_one_iff h2).mp hi)
    · have hc1' : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w) = 0 := by
        have := matchesBChar_le_one fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool w)
        omega
      simp only [Bool.or_eq_true]
      refine Or.inl ?_
      by_contra hcontra
      exact hc1 ((matchesBChar_eq_one_iff h1).mpr (by simpa using hcontra))
  · intro h i _
    rcases (show subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i = 0 ∨
        subsetGuardChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i = 1 from by
      have := subsetGuardChar_le_one fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) i
      omega) with hguard | hguard
    · rw [hguard, selectFn_zero]
    · rw [hguard, selectFn_one]
      unfold subsetGuardChar at hguard
      rw [mulBit_eq_one_iff, isOne_eq_one_iff] at hguard
      obtain ⟨hallbin, hlen0⟩ := hguard
      have hlenle : listLenChar i ≤
          Fintype.card (Finset (autState e1) × Finset (autState e2)) := by omega
      have hieq : c9b5_encodeListBool (c9b6_decodeListBool i) = i :=
        c9b6_encodeListBool_decodeListBool_of_allBin hallbin
      have hwlen : (c9b6_decodeListBool i).length ≤
          Fintype.card (Finset (autState e1) × Finset (autState e2)) := by
        unfold c9b6_decodeListBool
        rw [List.length_map]
        rwa [listLenChar_eq] at hlenle
      have hwmem := (mem_wordsUpTo _).mpr hwlen
      have hspec := h (c9b6_decodeListBool i) hwmem
      rw [← hieq]
      by_cases hc1 : matchesBChar fuel (c9b5_sexprGodelEncode e1) (c9b5_encodeListBool
          (c9b6_decodeListBool i)) = 1
      · rw [hc1, selectFn_one]
        have hc1matches : matchesB e1 (c9b6_decodeListBool i) = true :=
          (matchesBChar_eq_one_iff h1).mp hc1
        simp only [Bool.or_eq_true] at hspec
        rcases hspec with hf | ht
        · rw [hc1matches] at hf; simp at hf
        · exact (matchesBChar_eq_one_iff h2).mpr ht
      · have hc1' : matchesBChar fuel (c9b5_sexprGodelEncode e1)
            (c9b5_encodeListBool (c9b6_decodeListBool i)) = 0 := by
          have := matchesBChar_le_one fuel (c9b5_sexprGodelEncode e1)
            (c9b5_encodeListBool (c9b6_decodeListBool i))
          omega
        rw [hc1', selectFn_zero]

theorem consistentBChar_eq_one_iff {fuel : ℕ} {a b : SExpr}
    (h : c9b5_sexprDepth (.cap a b) ≤ fuel) :
    consistentBChar fuel (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b) = 1 ↔
      (denote (.cap a b)).Nonempty := by
  simp only [consistentBChar, ← c9b6_sexprGodelEncode_cap]
  exact decideNonemptyBChar_eq_one_iff h

theorem decideNonemptyBChar_le_one (fuel c_e : ℕ) : decideNonemptyBChar fuel c_e ≤ 1 :=
  bExistsFn_le_one _ _ _

theorem consistentBChar_le_one (fuel c1 c2 : ℕ) : consistentBChar fuel c1 c2 ≤ 1 :=
  decideNonemptyBChar_le_one _ _

theorem autStateCardFuelChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable autStateCardFuelCharLookup bound fuel) c 0 = autStateCardFuelChar fuel c :=
  fuelTable_eq_of_recursion (F := autStateCardFuelChar) (Body := autStateCardFuelCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold autStateCardFuelCharLookup; simp)
    autStateCardFuelCharBody_local

theorem interEqChar_eq_one_iff {fuel : ℕ} {e1 e2 : SExpr}
    (h1 : c9b5_sexprDepth e1 ≤ fuel) (h2 : c9b5_sexprDepth e2 ≤ fuel) :
    interEqChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) = 1 ↔
      denote e1 = denote e2 := by
  unfold interEqChar
  rw [mulBit_eq_one_iff, subsetBChar_eq_one_iff h1 h2, subsetBChar_eq_one_iff h2 h1,
    ← Set.Subset.antisymm_iff]

theorem matchesBChar_fuelTable_eq :
    ∀ fuel bound code, code ≤ bound →
      nthCode (fuelTable matchesBCharBodyLookup bound fuel) code 0 =
        matchesBChar fuel code.unpair.1 code.unpair.2 :=
  fuelTable_eq_of_recursion
    (F := fun fuel code => matchesBChar fuel code.unpair.1 code.unpair.2)
    (Body := fun prev code => matchesBCharBody prev code.unpair.1 code.unpair.2)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table code => by unfold matchesBCharBodyLookup; simp)
    (fun f g code h => matchesBCharBody_local f g code.unpair.1 code.unpair.2 (by
      simpa [pair_unpair] using h))

theorem primrec_autStateCardFuelChar : ∀ fuel, Nat.Primrec (fun c => autStateCardFuelChar fuel c)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [autStateCardFuelChar] using
      primrec_autStateCardFuelCharBody (primrec_autStateCardFuelChar fuel)

theorem primrec_autStateCardFuelCharLookup : Nat.Primrec autStateCardFuelCharLookup := by
  have hleft : Nat.Primrec (fun w => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by simp
  have hright : Nat.Primrec (fun w => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by simp
  have hadd : Nat.Primrec (fun w =>
      nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0 +
        nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    primrec_add₂ hleft hright
  have hmul : Nat.Primrec (fun w =>
      nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0 *
        nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    primrec_mul₂ hleft hright
  have hf0 : Nat.Primrec (fun _ : ℕ => (1 : ℕ)) := Nat.Primrec.const 1
  have hf1 : Nat.Primrec (fun w => listLenChar w.unpair.2.unpair.2 + 2) :=
    primrec_add₂ (primrec_listLenChar.comp (Nat.Primrec.right.comp Nat.Primrec.right))
      (Nat.Primrec.const 2)
  have ht : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have h01 : Nat.Primrec (fun w => isOne (1 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) ht)
  have h12 : Nat.Primrec (fun w => isOne (2 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) ht)
  have h23 : Nat.Primrec (fun w => isOne (3 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) ht)
  have h34 : Nat.Primrec (fun w => isOne (4 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) ht)
  refine (primrec_selectFn h01 hf0
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hadd
        (primrec_selectFn h34 hmul (Nat.Primrec.const 0))))).of_eq fun w => ?_
  show _ = autStateCardFuelCharBody (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2
  rw [autStateCardFuelCharBody_eq]
  match tag : w.unpair.2.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01' : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 2 : ℕ) = 0 := rfl
    have h23' : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01', h23', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 3 =>
    have h01' : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - 3 : ℕ) = 0 := rfl
    have h34' : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01', h34', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 4 =>
    have h01' : (1 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h34' : (4 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', h23', h34', isOne_zero, selectFn_zero]

theorem primrec_autStateCardFuelChar2 :
    Nat.Primrec (fun s => autStateCardFuelChar s.unpair.1 s.unpair.2) := by
  have hft := primrec_fuelTable primrec_autStateCardFuelCharLookup
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable autStateCardFuelCharLookup s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable autStateCardFuelCharLookup s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (Nat.Primrec.pair hcomp (Nat.Primrec.pair Nat.Primrec.right (Nat.Primrec.const 0)))).of_eq
      fun s => by simp
  exact hnth.of_eq fun s =>
    autStateCardFuelChar_fuelTable_eq s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)

theorem primrec_matchesBCatGLookup : Nat.Primrec matchesBCatGLookup := by
  have hi : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcw : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have ha : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have htake : Nat.Primrec (fun w => takeCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2) :=
    (primrec_takeCode.comp (Nat.Primrec.pair hi hcw)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hdrop : Nat.Primrec (fun w => dropCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2) :=
    (primrec_dropCode.comp (Nat.Primrec.pair hi hcw)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h1 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.1
        (takeCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2)) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.pair ha htake) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.2
        (dropCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2)) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.pair hb hdrop) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mul₂ h1 h2).of_eq fun w => by
    dsimp [matchesBCatGLookup, matchesBCatG, mulBit]

theorem primrec_matchesBChar : ∀ fuel, Nat.Primrec (fun t => matchesBChar fuel t.unpair.1 t.unpair.2)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [matchesBChar] using
      primrec_matchesBCharBody (primrec_matchesBChar fuel)

theorem primrec_decideNonemptyBChar (fuel : ℕ) :
    Nat.Primrec (fun c_e => decideNonemptyBChar fuel c_e) := by
  have hg : Nat.Primrec (fun w =>
      mulBit (allBinDigitsChar w.unpair.1) (matchesBChar fuel w.unpair.2 w.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair (primrec_allBinDigitsChar.comp Nat.Primrec.left)
      ((primrec_matchesBChar fuel).comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)))).of_eq
      fun w => by simp
  have hpack : Nat.Primrec (fun c_e =>
      Nat.pair c_e (codeBound (autStateCardFuelChar fuel c_e))) :=
    Nat.Primrec.pair Nat.Primrec.id
      (primrec_codeBound.comp (primrec_autStateCardFuelChar fuel))
  refine ((primrec_bExistsFn hg).comp hpack).of_eq fun c_e => ?_
  simp [decideNonemptyBChar]

theorem primrec_consistentBChar (fuel : ℕ) :
    Nat.Primrec (fun t => consistentBChar fuel t.unpair.1 t.unpair.2) :=
  (primrec_decideNonemptyBChar fuel).comp
    (Nat.Primrec.pair (Nat.Primrec.const 3)
      (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right))

set_option maxHeartbeats 4000000 in
theorem primrec_matchesBCharBodyLookup : Nat.Primrec matchesBCharBodyLookup := by
  have htable : Nat.Primrec (fun w => w.unpair.1) := Nat.Primrec.left
  have hc : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hcw : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have htag : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.1) := Nat.Primrec.left.comp hc
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  have h23 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) htag)
  have h34 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) htag)
  have hf1 : Nat.Primrec (fun w => listEqChar w.unpair.2.unpair.2 w.unpair.2.unpair.1.unpair.2) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hcw (Nat.Primrec.right.comp hc))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun w'' => matchesBCatGLookup
      (Nat.pair w''.unpair.2.unpair.1 (Nat.pair w''.unpair.1 w''.unpair.2.unpair.2))) :=
    (primrec_matchesBCatGLookup.comp (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
      (Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.right.comp Nat.Primrec.right)))).of_eq
      fun _ => rfl
  have hcatpack : Nat.Primrec (fun w => Nat.pair
      (Nat.pair w.unpair.1 (Nat.pair w.unpair.2.unpair.1 w.unpair.2.unpair.2))
      (listLenChar w.unpair.2.unpair.2 + 1)) :=
    Nat.Primrec.pair (Nat.Primrec.pair htable (Nat.Primrec.pair hc hcw))
      (primrec_add₂ (primrec_listLenChar.comp hcw) (Nat.Primrec.const 1))
  have hcat : Nat.Primrec (fun w => bExistsFn
      (fun w'' => matchesBCatGLookup
        (Nat.pair w''.unpair.2.unpair.1 (Nat.pair w''.unpair.1 w''.unpair.2.unpair.2)))
      (Nat.pair w.unpair.1 (Nat.pair w.unpair.2.unpair.1 w.unpair.2.unpair.2))
      (listLenChar w.unpair.2.unpair.2 + 1)) :=
    ((primrec_bExistsFn hg).comp hcatpack).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have ha : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hlk1 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.1.unpair.2.unpair.1 w.unpair.2.unpair.2) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair htable
      (Nat.Primrec.pair (Nat.Primrec.pair ha hcw) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hlk2 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.1.unpair.2.unpair.2 w.unpair.2.unpair.2) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair htable
      (Nat.Primrec.pair (Nat.Primrec.pair hb hcw) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hcap := primrec_mul₂ hlk1 hlk2
  refine (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hcat
        (primrec_selectFn h34 hcap (Nat.Primrec.const 0))))).of_eq fun w => ?_
  show _ = matchesBCharBody (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2.unpair.1 w.unpair.2.unpair.2
  rw [matchesBCharBody_eq]
  match tag : w.unpair.2.unpair.1.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01' : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 2 : ℕ) = 0 := rfl
    have h23' : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01', h23', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
    apply eq_of_le_one_iff_one (bExistsFn_le_one _ _ _) (bExistsFn_le_one _ _ _)
    rw [bExistsFn_eq_one_iff, bExistsFn_eq_one_iff]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    simp only [matchesBCatGLookup, unpair_pair_fst, unpair_pair_snd]
  | 3 =>
    have h01' : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - 3 : ℕ) = 0 := rfl
    have h34' : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01', h34', isOne_zero, isOne_one, selectFn_zero, selectFn_one,
      mulBit]
  | t + 4 =>
    have h01' : (1 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h34' : (4 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', h23', h34', isOne_zero, selectFn_zero]

theorem primrec_matchesBChar2 :
    Nat.Primrec (fun s => matchesBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hft := primrec_fuelTable primrec_matchesBCharBodyLookup
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable matchesBCharBodyLookup s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable matchesBCharBodyLookup s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (Nat.Primrec.pair hcomp (Nat.Primrec.pair Nat.Primrec.right (Nat.Primrec.const 0)))).of_eq
      fun s => by simp
  exact hnth.of_eq fun s => by
    rw [matchesBChar_fuelTable_eq s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)]

theorem primrec_decideNonemptyBChar2 :
    Nat.Primrec (fun s => decideNonemptyBChar s.unpair.1 s.unpair.2) := by
  have hg : Nat.Primrec (fun u => mulBit (allBinDigitsChar u.unpair.2.unpair.1)
      (matchesBChar u.unpair.1 u.unpair.2.unpair.2 u.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair
      (primrec_allBinDigitsChar.comp (Nat.Primrec.left.comp Nat.Primrec.right))
      (primrec_matchesBChar2.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
          (Nat.Primrec.left.comp Nat.Primrec.right)))))).of_eq fun u => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hbe := primrec_bExistsFn_param hg
  have hpack : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2)
      (codeBound (autStateCardFuelChar s.unpair.1 s.unpair.2))) :=
    Nat.Primrec.pair (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right)
      (primrec_codeBound.comp primrec_autStateCardFuelChar2)
  exact (hbe.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, decideNonemptyBChar]

theorem primrec_consistentBChar2 :
    Nat.Primrec (fun s => consistentBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hpack : Nat.Primrec (fun s => Nat.pair s.unpair.1
      (Nat.pair 3 (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))) :=
    Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.const 3)
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
          (Nat.Primrec.right.comp Nat.Primrec.right)))
  exact (primrec_decideNonemptyBChar2.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, consistentBChar, capCode]

theorem primrec_subsetBChar :
    Nat.Primrec (fun s => subsetBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hg : Nat.Primrec (fun u => selectFn
      (subsetGuardChar u.unpair.1 u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.2.unpair.2
        u.unpair.2.unpair.1)
      (selectFn (matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.1)
        (matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) 1) 1) := by
    have hfuel : Nat.Primrec (fun u : ℕ => u.unpair.1) := Nat.Primrec.left
    have hi : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.right
    have hc1 : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
    have hc2 : Nat.Primrec (fun u : ℕ => u.unpair.2.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
    have hguard : Nat.Primrec (fun u => subsetGuardChar u.unpair.1 u.unpair.2.unpair.2.unpair.1
        u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      have hbound : Nat.Primrec (fun u => subsetBoundChar u.unpair.1
          u.unpair.2.unpair.2.unpair.1 u.unpair.2.unpair.2.unpair.2) := by
        have h1 : Nat.Primrec (fun u => autStateCardFuelChar u.unpair.1
            u.unpair.2.unpair.2.unpair.1) := by
          have := primrec_autStateCardFuelChar2
          exact (this.comp (Nat.Primrec.pair hfuel hc1)).of_eq fun u => by
            simp only [unpair_pair_fst, unpair_pair_snd]
        have h2 : Nat.Primrec (fun u => autStateCardFuelChar u.unpair.1
            u.unpair.2.unpair.2.unpair.2) := by
          have := primrec_autStateCardFuelChar2
          exact (this.comp (Nat.Primrec.pair hfuel hc2)).of_eq fun u => by
            simp only [unpair_pair_fst, unpair_pair_snd]
        exact (primrec_mul₂ (primrec_pow₂ (Nat.Primrec.const 2) h1)
          (primrec_pow₂ (Nat.Primrec.const 2) h2))
      exact (primrec_mulBit.comp (Nat.Primrec.pair
        (primrec_allBinDigitsChar.comp hi)
        (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1)
          (primrec_sub₂ (primrec_listLenChar.comp hi) hbound))))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd, subsetGuardChar, mulBit]
    have hm1 : Nat.Primrec (fun u => matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.1
        u.unpair.2.unpair.1) := by
      have := primrec_matchesBChar2
      exact (this.comp (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc1 hi))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have hm2 : Nat.Primrec (fun u => matchesBChar u.unpair.1 u.unpair.2.unpair.2.unpair.2
        u.unpair.2.unpair.1) := by
      have := primrec_matchesBChar2
      exact (this.comp (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc2 hi))).of_eq fun u => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    exact primrec_selectFn hguard (primrec_selectFn hm1 hm2 (Nat.Primrec.const 1))
      (Nat.Primrec.const 1)
  have hb := primrec_bForallFn_param hg
  have hpack : Nat.Primrec (fun s => Nat.pair
      (Nat.pair s.unpair.1 (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))
      (codeBound (subsetBoundChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2))) := by
    have hfuel : Nat.Primrec (fun s : ℕ => s.unpair.1) := Nat.Primrec.left
    have hc1 : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) :=
      Nat.Primrec.left.comp Nat.Primrec.right
    have hc2 : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.right
    have h1 : Nat.Primrec (fun s => autStateCardFuelChar s.unpair.1 s.unpair.2.unpair.1) := by
      have := primrec_autStateCardFuelChar2
      exact (this.comp (Nat.Primrec.pair hfuel hc1)).of_eq fun s => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have h2 : Nat.Primrec (fun s => autStateCardFuelChar s.unpair.1 s.unpair.2.unpair.2) := by
      have := primrec_autStateCardFuelChar2
      exact (this.comp (Nat.Primrec.pair hfuel hc2)).of_eq fun s => by
        simp only [unpair_pair_fst, unpair_pair_snd]
    have hbnd : Nat.Primrec (fun s => subsetBoundChar s.unpair.1 s.unpair.2.unpair.1
        s.unpair.2.unpair.2) :=
      primrec_mul₂ (primrec_pow₂ (Nat.Primrec.const 2) h1) (primrec_pow₂ (Nat.Primrec.const 2) h2)
    exact Nat.Primrec.pair (Nat.Primrec.pair hfuel (Nat.Primrec.pair hc1 hc2))
      (primrec_codeBound.comp hbnd)
  exact (hb.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, subsetBChar]

theorem primrec_interEqChar :
    Nat.Primrec (fun s => interEqChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hswap : Nat.Primrec (fun s : ℕ =>
      Nat.pair s.unpair.1 (Nat.pair s.unpair.2.unpair.2 s.unpair.2.unpair.1)) :=
    Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
        (Nat.Primrec.left.comp Nat.Primrec.right))
  have h1 := primrec_subsetBChar
  have h2 : Nat.Primrec (fun s => subsetBChar s.unpair.1 s.unpair.2.unpair.2 s.unpair.2.unpair.1) :=
    (primrec_subsetBChar.comp hswap).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mulBit.comp (Nat.Primrec.pair h1 h2)).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, interEqChar]

theorem subsetBChar_le_one (fuel c1 c2 : ℕ) : subsetBChar fuel c1 c2 ≤ 1 := by
  unfold subsetBChar; exact bForallFn_le_one _ _ _

theorem interEqChar_le_one (fuel c1 c2 : ℕ) : interEqChar fuel c1 c2 ≤ 1 := by
  unfold interEqChar; exact mulBit_le_one (subsetBChar_le_one _ _ _) (subsetBChar_le_one _ _ _)

end Domain.Recursive

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

namespace RegularLanguage
open Set Domain.Recursive

variable {α : Type*}

structure ConsistencyPresentation (V : NeighborhoodSystem α) where

  X : ℕ → Set α

  mem_X : ∀ n, V.mem (X n)

  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y

  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

end RegularLanguage
end DomainTheory.NeighbourhoodSystems
