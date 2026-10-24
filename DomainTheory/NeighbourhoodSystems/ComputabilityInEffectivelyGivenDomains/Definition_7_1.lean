module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_22

public import Mathlib.Computability.Primrec.Basic

public import Mathlib.Data.Nat.Bitwise

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability
open Sum Set
section
variable {σ₁ σ₂ : Type}
variable {σ : Type}
/- concordance: source L4243 DEFINITION 7.1 computable presentation -/
/-- **Definition 7.1 (ii) for encoded neighbourhoods:** when `denote a`, `denote b ∈ S`,
`consistentB` agrees with membership of the intersection in `S`. -/
theorem consistentB_iff_Ssys (a b : SExpr) (ha : InS (denote a)) (hb : InS (denote b)) :
    consistentB a b = true ↔ InS (denote a ∩ denote b) := by
  rw [← denote_cap, consistentB_iff]
  exact Iff.symm (Ssys_isPositive (Ssys_mem.mpr ha) (Ssys_mem.mpr hb))
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_decide : ∀ (a b : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  DomainTheory.NeighbourhoodSystems.Exercise722.InS (DomainTheory.NeighbourhoodSystems.Exercise722.denote a) →
    DomainTheory.NeighbourhoodSystems.Exercise722.InS (DomainTheory.NeighbourhoodSystems.Exercise722.denote b) →
      Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.consistentB a b) Bool.true)
        (DomainTheory.NeighbourhoodSystems.Exercise722.InS
          (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool))
            (DomainTheory.NeighbourhoodSystems.Exercise722.denote a)
            (DomainTheory.NeighbourhoodSystems.Exercise722.denote b))) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.consistentB_iff_Ssys
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability
open Sum Set

section
variable {σ₁ σ₂ : Type}
variable {σ : Type}

/-- **Definition 7.1 relation (ii) as a reachability problem.** `denote e` is empty iff no accept
state of its `Fintype` automaton is reachable. The right-hand side ranges over the finite state set
`autState e`; the only non-finite-looking quantifier (`∀ x`) is what a reachability search eliminates. -/
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

/-- A nonempty accepted language ⟺ some accept state is reachable by reading some word. -/
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

section
/-- The accept states of `toNFA e`, as a `Finset`. -/
def acceptFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)}
  | .cap a b => (acceptFin a) ×ˢ (acceptFin b)
  | .cat a b => (acceptFin b).image (inr : autState b → autState a ⊕ autState b)
end

section
/-- The start states of `toNFA e`, as a `Finset`. The `.cat` case handles the one-hop
ε-closure directly (`catEps`'s only ε-edges go from an `M₁`-accept state to `M₂`-start states,
`catEps_mem_εClosure_iff`): if some start state of `a` is already accepting, `b`'s start states
are also immediately live. -/
def startFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)}
  | .cap a b => (startFin a) ×ˢ (startFin b)
  | .cat a b =>
      if ((startFin a) ∩ (acceptFin a)).Nonempty
      then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
        (startFin b).image (inr : autState b → autState a ⊕ autState b)
      else (startFin a).image (inl : autState a → autState a ⊕ autState b)
end

section
/-- The step function of `toNFA e` from a single state, as a `Finset`. The `.cat` case's `inl`
branch mirrors `startFin`'s epsilon-closure handling exactly (one hop, on reaching an `a`-accept
state after the step). -/
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
end

section
/-- The `Finset`-lifted step (mirrors `NFA.stepSet`). -/
def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)
end

section
/-- Tracks `(evalFin e₁ w, evalFin e₂ w)` deterministically; accepts `w` iff `e₁` is live-accepting
and `e₂` is not — i.e. `w ∈ denote e₁ \ denote e₂`. -/
def diffNFA (e1 e2 : SExpr) : NFA Bool (Finset (autState e1) × Finset (autState e2)) where
  step S c := {(stepFin e1 S.1 c, stepFin e2 S.2 c)}
  start := {(startFin e1, startFin e2)}
  accept := {S | (S.1 ∩ acceptFin e1).Nonempty ∧ S.2 ∩ acceptFin e2 = ∅}
end

section
/-- The live-state `Finset` after reading `w` (mirrors `NFA.eval`, folding `stepFin` left to
right from `startFin`). -/
def evalFin (e : SExpr) (w : List Bool) : Finset (autState e) :=
  w.foldl (stepFin e) (startFin e)
end

section
/-- `denote e₁ ⊆ denote e₂`, decided by a bounded search: if no word up to the `diffNFA` state
bound witnesses `e₁ \ e₂`, none exists at all (`exists_diff_word_short`). -/
def subsetB (e1 e2 : SExpr) : Bool :=
  (wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2)))).all
    (fun w => !matchesB e1 w || matchesB e2 w)
end

section
/-- **Exercise 7.22k.** Relation (i) on `SExpr` syntax — language equivalence — decided by
`subsetB` in both directions. -/
def interEqB (e1 e2 : SExpr) : Bool := subsetB e1 e2 && subsetB e2 e1
end

section
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
end

section
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
end

section
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
end

section
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
end

section
theorem coe_foldl_stepFin (e : SExpr) (w : List Bool) (S : Finset (autState e)) :
    (↑(w.foldl (stepFin e) S) : Set (autState e)) = (toNFA e).evalFrom ↑S w := by
  induction w generalizing S with
  | nil => rfl
  | cons c w ih =>
    show (↑(w.foldl (stepFin e) (stepFin e S c)) : Set (autState e)) = _
    rw [ih (stepFin e S c), NFA.evalFrom_cons, coe_stepFin e S c]
end

section
theorem coe_evalFin (e : SExpr) (w : List Bool) :
    (↑(evalFin e w) : Set (autState e)) = (toNFA e).eval w := by
  show (↑(w.foldl (stepFin e) (startFin e)) : Set (autState e))
    = (toNFA e).evalFrom (toNFA e).start w
  rw [coe_foldl_stepFin e w (startFin e), coe_startFin e]
end

section
/-- **`denote e` via the `Finset` simulation.** `w` matches `e` iff some live state after reading
`w` is accepting — a decidable `Finset` intersection test. -/
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
end

section
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
end

section
theorem diffNFA_eval (e1 e2 : SExpr) (w : List Bool) :
    (diffNFA e1 e2).eval w = {(evalFin e1 w, evalFin e2 w)} := by
  show (diffNFA e1 e2).evalFrom (diffNFA e1 e2).start w = _
  show (diffNFA e1 e2).evalFrom {(startFin e1, startFin e2)} w = _
  exact diffNFA_evalFrom e1 e2 w (startFin e1) (startFin e2)
end

section
/-- **`diffNFA` accepts exactly `denote e₁ \ denote e₂`.** -/
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
end

section
/-- **The shortest witness of `denote e₁ ⊄ denote e₂`, if any, is short.** Generic
`exists_accepted_word_short` applied to `diffNFA`. -/
theorem exists_diff_word_short {e1 e2 : SExpr} (h : ¬ denote e1 ⊆ denote e2) :
    ∃ w, w.length < Fintype.card (Finset (autState e1) × Finset (autState e2)) ∧
      w ∈ denote e1 ∧ w ∉ denote e2 := by
  rw [Set.not_subset] at h
  have hne : (diffNFA e1 e2).accepts.Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := h
    exact ⟨x, (diffNFA_mem_accepts_iff e1 e2 x).mpr ⟨hx1, hx2⟩⟩
  obtain ⟨w, hlen, hmem⟩ := exists_accepted_word_short hne
  exact ⟨w, hlen, (diffNFA_mem_accepts_iff e1 e2 w).mp hmem⟩
end

section
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
end

section
theorem interEqB_iff (e1 e2 : SExpr) : interEqB e1 e2 = true ↔ denote e1 = denote e2 := by
  unfold interEqB
  rw [Bool.and_eq_true, subsetB_iff, subsetB_iff, ← Set.Subset.antisymm_iff]
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_equiv : ∀ (e1 e2 : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.interEqB e1 e2) Bool.true)
    (@Eq (Set (List Bool)) (DomainTheory.NeighbourhoodSystems.Exercise722.denote e1)
      (DomainTheory.NeighbourhoodSystems.Exercise722.denote e2)) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.interEqB_iff
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace Domain.Recursive
open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

section
/-- **AM–GM for naturals (choice-free).** `4 a b ≤ (a+b)²`. Faithful port of mathlib's `private`
`Nat.AM_GM` (no classical tactics). -/
theorem amGM : ∀ {a b : ℕ}, 4 * a * b ≤ (a + b) * (a + b)
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact Nat.zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@amGM a b) 4
end

section
/-- **Choice-free `sqrt.iter` lower bound.** `iter n guess ² ≤ n`. Faithful port of
`Nat.sqrt.iter_sq_le`, with `grind` replaced by `omega`. -/
theorem iter_sq_le (n guess : ℕ) : Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dite_eq_left h]
    exact iter_sq_le n ((guess + n / guess) / 2)
  else
    rw [dite_eq_right h]
    apply Nat.mul_le_of_le_div
    omega
  termination_by guess
  decreasing_by exact h
end

section
/-- Choice-free left-cancellation for `<` under `*` (mathlib's `Nat.lt_of_mul_lt_mul_left` is
classical). From `a*b < a*c` deduce `b < c`, by the contrapositive `c ≤ b → a*c ≤ a*b`. -/
theorem lt_of_mul_lt_mul_left' {a b c : ℕ} (h : a * b < a * c) : b < c := by
  rcases Nat.lt_or_ge b c with hbc | hbc
  · exact hbc
  · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_left a hbc))
end

section
/-- **Choice-free `sqrt.iter` upper bound.** If `n < (guess+1)²` then `n < (iter n guess + 1)²`.
Faithful port of `Nat.sqrt.lt_iter_succ_sq`, with `lia` replaced by `omega`. -/
theorem lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dite_eq_left h]
    suffices hsuff : n < ((guess + n / guess) / 2 + 1) * ((guess + n / guess) / 2 + 1) from
      lt_iter_succ_sq n ((guess + n / guess) / 2) hsuff
    refine lt_of_mul_lt_mul_left' (a := 4 * (guess * guess)) ?_
    apply Nat.lt_of_le_of_lt amGM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← Nat.add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux : (guess + n / guess + 1) ≤ 2 * ((guess + n / guess + 1 + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left
      (Nat.lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le _) h)) _
  else
    rw [dite_eq_right h]
    exact hn
  termination_by guess
  decreasing_by exact h
end

section
/-- `n < (sqrt n + 1)²` (choice-free; mathlib's `Nat.lt_succ_sqrt` is classical). The initial guess
`2 ^ (log₂ n / 2 + 1)` over-shoots `√n`, which feeds `lt_iter_succ_sq`. -/
theorem lt_succ_sqrt (n : ℕ) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, ite_eq_right (Nat.not_le.mpr h)]
    refine lt_iter_succ_sq _ _ ?_
    set g := 1 <<< (n.log2 / 2 + 1) with hg
    have hshift : g = 2 ^ (n.log2 / 2 + 1) := by rw [hg, Nat.shiftLeft_eq, Nat.one_mul]
    have hgg : g * g = 2 ^ (2 * (n.log2 / 2 + 1)) := by
      rw [hshift, ← pow_add]; congr 1; omega
    calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ (2 * (n.log2 / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = g * g := hgg.symm
      _ ≤ (g + 1) * (g + 1) := Nat.mul_le_mul (Nat.le_succ g) (Nat.le_succ g)
  · rw [Nat.sqrt, ite_eq_left h]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n))
end

section
/-- `sqrt n` squared is `≤ n` (choice-free; mathlib's `Nat.sqrt_le` is classical). -/
theorem sqrt_le (n : ℕ) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, ite_eq_right (Nat.not_le.mpr h)]
    exact iter_sq_le _ _
  · rw [Nat.sqrt, ite_eq_left h]
    calc n * n ≤ 1 * n := Nat.mul_le_mul_right n h
      _ = n := Nat.one_mul n
end

section
/-- **The square-root characterization (choice-free).** If `q² ≤ m < (q+1)²` then `sqrt m = q`. The
uniqueness step is `omega` from the two bounds plus `sqrt_le`/`lt_succ_sqrt`. -/
theorem sqrt_eq_of {m q : ℕ} (h1 : q * q ≤ m) (h2 : m < (q + 1) * (q + 1)) : Nat.sqrt m = q := by
  have hle := sqrt_le m
  have hlt := lt_succ_sqrt m
  have hq_le : q ≤ Nat.sqrt m := by
    rcases Nat.lt_or_ge (Nat.sqrt m) q with hh | hh
    · exfalso
      have ha : Nat.sqrt m + 1 ≤ q := hh
      have hmul : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ q * q := Nat.mul_le_mul ha ha
      omega
    · exact hh
  have hle_q : Nat.sqrt m ≤ q := by
    rcases Nat.lt_or_ge q (Nat.sqrt m) with hh | hh
    · exfalso
      have ha : q + 1 ≤ Nat.sqrt m := hh
      have hmul : (q + 1) * (q + 1) ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul ha ha
      omega
    · exact hh
  omega
end

section
/-- `sqrt (q² + a) = q` whenever `a ≤ 2q` (choice-free; mathlib's `Nat.sqrt_add_eq` is classical). -/
theorem sqrt_add_eq (q a : ℕ) (h : a ≤ q + q) : Nat.sqrt (q * q + a) = q := by
  refine sqrt_eq_of (Nat.le_add_right _ _) ?_
  have expand : (q + 1) * (q + 1) = q * q + q + q + 1 := Nat.succ_mul_succ q q
  omega
end

section
/-- **`unpair ∘ pair = id` (choice-free).** Mirrors `Nat.unpair_pair`. -/
theorem unpair_pair (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b) := by
  rw [Nat.pair]
  if h : a < b then
    rw [ite_eq_left h]
    show Nat.unpair (b * b + a) = (a, b)
    have be : Nat.sqrt (b * b + a) = b := sqrt_add_eq b a (by omega)
    simp only [Nat.unpair, be, Nat.add_sub_cancel_left, ite_eq_left h]
  else
    rw [ite_eq_right h]
    show Nat.unpair (a * a + a + b) = (a, b)
    have ae : Nat.sqrt (a * a + a + b) = a := by
      have e : a * a + a + b = a * a + (a + b) := by omega
      rw [e]; exact sqrt_add_eq a (a + b) (by omega)
    have e1 : a * a + a + b - a * a = a + b := by omega
    have e2 : ¬ a + b < a := by omega
    have e3 : a + b - a = b := by omega
    simp only [Nat.unpair, ae, e1, ite_eq_right e2, e3]
end

section
@[simp] theorem unpair_pair_fst (a b : ℕ) : (Nat.pair a b).unpair.1 = a := by rw [unpair_pair]
end

section
@[simp] theorem unpair_pair_snd (a b : ℕ) : (Nat.pair a b).unpair.2 = b := by rw [unpair_pair]
end

section
/-- Choice-free primitive-recursive **selection**: `selectFn c a b = a` if `c = 1`, `= b` if `c = 0`
(for a `{0,1}`-valued `c`), via `c * a + (1 - c) * b`. -/
def selectFn (c a b : ℕ) : ℕ := c * a + (1 - c) * b
end

section
@[simp] theorem selectFn_one (a b : ℕ) : selectFn 1 a b = a := by simp [selectFn]
end

section
@[simp] theorem selectFn_zero (a b : ℕ) : selectFn 0 a b = b := by simp [selectFn]
end

section
@[simp] theorem selectFn_ite {c : Prop} [Decidable c] (a b : ℕ) :
    selectFn (if c then 1 else 0) a b = if c then a else b := by
  split <;> simp [selectFn]
end

section
/-- A unary predicate `p : ℕ → Prop` is **recursively decidable**. -/
def RecDecidable (p : ℕ → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Nat.Primrec f ∧ ∀ n, p n ↔ f n = 1
end

section
/-- A unary predicate `p : ℕ → Prop` is **recursively enumerable**: it is the projection of a
recursively decidable relation, `p n ↔ ∃ i, q (Nat.pair i n)`. -/
def REPred (p : ℕ → Prop) : Prop :=
  ∃ q : ℕ → Prop, RecDecidable q ∧ ∀ n, p n ↔ ∃ i, q (Nat.pair i n)
end

section
/-- A binary relation is recursively enumerable when its `Nat.pair`-coding is. -/
def REPred₂ (r : ℕ → ℕ → Prop) : Prop :=
  REPred fun t => r t.unpair.1 t.unpair.2
end

section
/-- A binary relation is recursively decidable when its `Nat.pair`-coding is. -/
def RecDecidable₂ (r : ℕ → ℕ → Prop) : Prop :=
  RecDecidable fun t => r t.unpair.1 t.unpair.2
end

section
/-- A ternary relation is recursively decidable when its `Nat.pair`-coding (`pair n (pair m k)`) is. -/
def RecDecidable₃ (r : ℕ → ℕ → ℕ → Prop) : Prop :=
  RecDecidable fun t => r t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
end

section
/-- Encode a list of naturals as a single natural: `[] ↦ 0`, `a :: l ↦ pair a (encodeList l) + 1`.
The `+1` keeps the empty list (code `0`) distinguishable from any nonempty list. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encodeList l) + 1
end

section
/-- One step of the code-walking fold. The state `s = pair rc acc` carries the remaining code `rc`
and accumulator `acc`. If `rc = 0` the state is a fixed point; otherwise `rc - 1 = pair head tail`,
and the step pops `head`, recurses on `tail`, and updates `acc := stp (pair head (pair acc params))`. -/
def foldStep (stp : ℕ → ℕ) (params s : ℕ) : ℕ :=
  selectFn (1 - s.unpair.1) s
    (Nat.pair (s.unpair.1 - 1).unpair.2
      (stp (Nat.pair (s.unpair.1 - 1).unpair.1 (Nat.pair s.unpair.2 params))))
end

section
/-- Fold the list coded by `c`, threading accumulator `z` and parameter `params`. Implemented as
`c`-fold iteration of `foldStep` from the initial state `pair c z`, projecting out the accumulator. -/
def foldCode (stp : ℕ → ℕ) (params z c : ℕ) : ℕ :=
  ((foldStep stp params)^[c] (Nat.pair c z)).unpair.2
end

section
/-- `halfParity n = pair (n / 2) (n % 2)`, built by structural recursion: from `(h, p)` for `n`, the
value for `n+1` is `(h + p, 1 - p)` (carry on odd→even). -/
def halfParity (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun _ ih => Nat.pair (ih.unpair.1 + ih.unpair.2) (1 - ih.unpair.2)) n
end

section
/-- Indicator of `v = 1`, as a `{0,1}`-valued primitive-recursive function. -/
def isOne (v : ℕ) : ℕ := 1 - ((v - 1) + (1 - v))
end

section
theorem isOne_eq_one_iff (v : ℕ) : isOne v = 1 ↔ v = 1 := by
  unfold isOne; constructor <;> (intro h; omega)
end

section
@[simp] theorem isOne_one : isOne 1 = 1 := (isOne_eq_one_iff 1).2 rfl
end

section
@[simp] theorem isOne_zero : isOne 0 = 0 := by unfold isOne; omega
end

section
/-- AND-fold step (`foldCode` shape): `acc ↦ acc ∧ isOne (g ⟨head, params⟩)`. -/
def allListStp (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 (isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) 0
end

section
/-- The `{0,1}` flag of the bounded `∀ e ∈ decodeList c, g ⟨e, p⟩ = 1`. -/
def allListChar (g : ℕ → ℕ) (p c : ℕ) : ℕ := foldCode (allListStp g) p 1 c
end

section
/-- The `{0,1}`-valued bounded-`∃` indicator: `1` iff `∃ i < N, g (pair i n) = 1`. Folded
right-to-left with `selectFn` so the result stays in `{0,1}`. -/
def bExistsFn (g : ℕ → ℕ) (n N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => selectFn ih 1 (isOne (g (Nat.pair i n)))) N
end

section
/-- The `{0,1}`-valued bounded-`∀` indicator: `1` iff `g (pair i n) = 1` for all `i < N`. Folded
right-to-left with `selectFn` so the result stays in `{0,1}`. -/
def bForallFn (g : ℕ → ℕ) (n N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 1 (fun i ih => selectFn ih (isOne (g (Nat.pair i n))) 0) N
end

section
/-- OR-fold step (`foldCode` shape): `acc ↦ acc ∨ isOne (g ⟨head, params⟩)`. -/
def existsListStp (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 1 (isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2)))
end

section
/-- The `{0,1}` flag of the bounded `∃ e ∈ decodeList c, g ⟨e, p⟩ = 1`. -/
def existsListChar (g : ℕ → ℕ) (p c : ℕ) : ℕ := foldCode (existsListStp g) p 0 c
end

section
/-- `{0,1}` flag: `1` iff `n` encodes a binary digit (`0` or `1`). -/
def isBinDigit (n : ℕ) : ℕ :=
  selectFn (isOne (1 - n)) 1 (selectFn (isOne (2 - n)) 1 0)
end

section
/-- `{0,1}` flag: every entry of `decodeList c` is a binary digit. -/
def allBinDigitsChar (c : ℕ) : ℕ :=
  allListChar (fun t => isBinDigit t.unpair.1) 0 c
end

section
/-- `{0,1}` test for `n = 0`. -/
def isZero (n : ℕ) : ℕ := 1 - min n 1
end

section
/-- `b ≤ pair a b` (choice-free; avoids mathlib's `Nat.right_le_pair` to keep the axiom set clean). -/
theorem le_pair_right (a b : ℕ) : b ≤ Nat.pair a b := by
  have hbb : b ≤ b * b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left b h
  unfold Nat.pair
  split <;> omega
end

section
set_option maxHeartbeats 800000 in

/-- Length fold step: ignore head/params, increment accumulator. -/
def listLenStp (w : ℕ) : ℕ := w.unpair.2.unpair.1 + 1
end

section
set_option maxHeartbeats 800000 in

/-- Coded list length: `(decodeList c).length`. -/
def listLenChar (c : ℕ) : ℕ := foldCode listLenStp 0 0 c
end

section
/-- The low-bit OR `(x ||| y) % 2`, in arithmetic `{0,1}`-valued form (so it is primitive recursive
without referring to `Nat.lor`). Equal to `(x ||| y) % 2` by `lowOr_eq_mod`. -/
def lowOr (x y : ℕ) : ℕ := 1 - (1 - (x % 2 + y % 2))
end

section
/-- Packed iteration state `pair (pair curA curB) (pair weight acc)` for the bitwise-OR fold. -/
def lorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowOr s.unpair.1.unpair.1 s.unpair.1.unpair.2))
end

section
/-- Prepend the *pair* `⟨n, x⟩` onto the list coded by `acc`. -/
def mapPairStep (n acc x : ℕ) : ℕ := Nat.pair (Nat.pair n x) acc + 1
end

section
/-- `foldCode`-shaped wrapper of `mapPairStep` (parameter `n` threaded via the `params` slot). -/
def mapPairStp (w : ℕ) : ℕ :=
  mapPairStep w.unpair.2.unpair.2 w.unpair.2.unpair.1 w.unpair.1
end

section
/-- **`mapPairCode n c`** codes the list `(decodeList c).map ⟨n, ·⟩` (reversed). -/
def mapPairCode (n c : ℕ) : ℕ := foldCode mapPairStp n 0 c
end

section
set_option maxHeartbeats 800000 in

/-- `{0,1}` AND on flags (both must be `1`). -/
def mulBit (a b : ℕ) : ℕ := a * b
end

section
set_option maxHeartbeats 800000 in

/-- One step of fuel-bounded decode-ok (previous fuel level supplied as `prev`). -/
def decodeFuelOkCharBody (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  let sub := mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)
  selectFn (isOne (1 - c.unpair.1))
    (selectFn (isOne (1 - c.unpair.2)) 1 0)
    (selectFn (isOne (2 - c.unpair.1)) (allBinDigitsChar c.unpair.2)
      (selectFn (isOne (3 - c.unpair.1)) sub
        (selectFn (isOne (4 - c.unpair.1)) sub 0)))
end

section
set_option maxHeartbeats 800000 in

/-- `{0,1}` flag: `1` iff fuel-bounded `SExpr` decode succeeds on code `c`. -/
def decodeFuelOkChar : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => decodeFuelOkCharBody (decodeFuelOkChar fuel) c
end

section
/-- The iterative bitwise OR: iterate `lorStep` `a + b` times (enough to consume every set bit of `a`
and `b`) from the initial state, and read off the accumulator. -/
def myLor (a b : ℕ) : ℕ :=
  (lorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
end

section
set_option maxHeartbeats 800000 in

/-- `{0,1}` nat-equality char (reused in C9b tag/element comparisons). -/
def natEqChar (a b : ℕ) : ℕ := 1 - ((a - b) + (b - a))
end

section
set_option maxHeartbeats 800000 in

@[simp] theorem natEqChar_eq_one_iff (a b : ℕ) : natEqChar a b = 1 ↔ a = b := by
  unfold natEqChar; omega
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- One fuel step of state-card counting (previous fuel level as `prev`). -/
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
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- Fuel-bounded mirror of `autStateCard` on Gödel codes. -/
def autStateCardFuelChar : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => autStateCardFuelCharBody (autStateCardFuelChar fuel) c
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- **Not** `private`: `Exercise722Presentation.lean` (downstream of this file via `Definition71`)
bridges this to its own `boolNat` in Session **C9b7**, since `Recursive.lean` cannot import
`Exercise722Presentation.lean` (would cycle) and so cannot state that bridge itself. -/
def c9b5_boolNat (b : Bool) : ℕ := if b then 1 else 0
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

def c9b5_encodeListBool (σ : List Bool) : ℕ := encodeList (σ.map c9b5_boolNat)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

def c9b5_sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)
  | .cap a b => 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- Gödel code mirroring `SExpr.encode` in `Exercise722Presentation.lean`. -/
def c9b5_sexprGodelEncode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (c9b5_encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))
  | .cap a b => Nat.pair 3 (Nat.pair (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b))
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Tag-3 cap code matching `SExpr.encode` / `c9b5_sexprGodelEncode`. -/
def capCode (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Upper bound on Gödel codes of `{0,1}`-lists of length at most `n`. -/
def codeBound : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.pair 1 (codeBound n) + 1
end

section
set_option maxHeartbeats 800000 in

/-- Non-empty-`remC2` branch of `listEqStp`. -/
def listEqStpNonzero (w : ℕ) : ℕ :=
  Nat.pair
    (selectFn w.unpair.2.unpair.1.unpair.1
      (natEqChar w.unpair.1 ((w.unpair.2.unpair.1.unpair.2 - 1).unpair.1)) 0)
    ((w.unpair.2.unpair.1.unpair.2 - 1).unpair.2)
end

section
set_option maxHeartbeats 800000 in

/-- Fold step: state `pair flag remC2`; consume one head of `c1`, peel one cons off `remC2`. -/
def listEqStp (w : ℕ) : ℕ :=
  selectFn (isZero w.unpair.2.unpair.1.unpair.2) (Nat.pair 0 0) (listEqStpNonzero w)
end

section
set_option maxHeartbeats 800000 in

/-- `listEqChar c1 c2 = 1 ↔ decodeList c1 = decodeList c2`. -/
def listEqChar (c1 c2 : ℕ) : ℕ :=
  let r := foldCode listEqStp 0 (Nat.pair 1 c2) c1
  mulBit r.unpair.1 (isZero r.unpair.2)
end

section
set_option maxHeartbeats 800000 in

def listEqStep (st x : ℕ) : ℕ := listEqStp (Nat.pair x (Nat.pair st 0))
end

section
set_option maxHeartbeats 800000 in

/-- `foldCode`-shaped indexing step. State `pair counter result`, parameter the target index `i`;
bump the counter and overwrite the result exactly when `counter = i` (via the `{0,1}` equality bit
`1 - ((counter - i) + (i - counter))`). -/
def nthStp (w : ℕ) : ℕ :=
  Nat.pair (w.unpair.2.unpair.1.unpair.1 + 1)
    (selectFn (1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
        + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1)))
      w.unpair.1 w.unpair.2.unpair.1.unpair.2)
end

section
set_option maxHeartbeats 800000 in

/-- **Primitive-recursive indexing into a coded list.** `nthCode c i d = (decodeList c).getD i d`. -/
def nthCode (c i d : ℕ) : ℕ := (foldCode nthStp i (Nat.pair 0 d) c).unpair.2
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Tabulation lookup for `appendListCode`: params `pair c1 (pair c2 len1)`. -/
def appendListTabFn (w : ℕ) : ℕ :=
  let i := w.unpair.1
  let p := w.unpair.2
  let len1 := p.unpair.2.unpair.2
  selectFn (isZero ((i + 1) - len1))
    (nthCode p.unpair.1 i 0)
    (nthCode p.unpair.2.unpair.1 (i - len1) 0)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- `autStateCardFuelCharBody`'s step, with `prev` replaced by table lookup. -/
def autStateCardFuelCharLookup (w : ℕ) : ℕ :=
  autStateCardFuelCharBody (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2
end

section
set_option maxHeartbeats 800000 in

/-- `decodeFuelOkCharBody`'s step, with `prev` replaced by table lookup: `w.unpair.1` is the
previous fuel level's table, `w.unpair.2` is the code being queried. -/
def decodeFuelOkCharLookup (w : ℕ) : ℕ :=
  decodeFuelOkCharBody (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Tabulation lookup for `dropCode`: params `pair n c`. -/
def dropListTabFn (w : ℕ) : ℕ :=
  nthCode (w.unpair.2.unpair.2) (w.unpair.1 + w.unpair.2.unpair.1) 0
end

section
/-- The pure (set-theoretic) witness-threading fold step. The accumulator is `pair remWitness flag`:
at the list head `x` we pop a witness `i` (the `decodeList` head of `remWitness`, i.e.
`(remWitness - 1).unpair.1`) with new remaining code `(remWitness - 1).unpair.2`, and `AND` the flag
with `isOne (qc ⟨i, x⟩)`. -/
def reForallF (qc : ℕ → ℕ) (acc x : ℕ) : ℕ :=
  Nat.pair (acc.unpair.1 - 1).unpair.2
    (selectFn acc.unpair.2 (isOne (qc (Nat.pair (acc.unpair.1 - 1).unpair.1 x))) 0)
end

section
/-- The `foldCode`-form step (parameter unused), used to package `reForallF` primitive-recursively. -/
def reForallStp (qc : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.2
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1))) 0)
end

section
/-- The `{0,1}`-flag computed by threading witness code `w` through the list coded by `c`. -/
def reForallChar (qc : ℕ → ℕ) (w c : ℕ) : ℕ :=
  (foldCode (reForallStp qc) 0 (Nat.pair w 1) c).unpair.2
end

section
/-- `n ≤ (sqrt n)² + 2·sqrt n` (choice-free; needed for `pair_unpair`). -/
theorem sqrt_le_add (n : ℕ) : n ≤ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n := by
  have h := lt_succ_sqrt n
  have e : (Nat.sqrt n + 1) * (Nat.sqrt n + 1)
      = Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n + 1 := Nat.succ_mul_succ _ _
  omega
end

section
/-- **`pair ∘ unpair = id` (choice-free).** Mirrors `Nat.pair_unpair`. -/
theorem pair_unpair (n : ℕ) : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := by
  have sm : Nat.sqrt n * Nat.sqrt n + (n - Nat.sqrt n * Nat.sqrt n) = n :=
    Nat.add_sub_cancel' (sqrt_le _)
  have hadd := sqrt_le_add n
  rw [Nat.unpair]
  if h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then
    rw [ite_eq_left h]
    show Nat.pair (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n) = n
    rw [Nat.pair, ite_eq_left h]
    omega
  else
    rw [ite_eq_right h]
    have hge : Nat.sqrt n ≤ n - Nat.sqrt n * Nat.sqrt n := Nat.le_of_not_lt h
    have hlt : ¬ Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by omega
    show Nat.pair (Nat.sqrt n) (n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n) = n
    rw [Nat.pair, ite_eq_right hlt]
    omega
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Numeric mirror of `Fintype.card (Finset (autState e₁) × Finset (autState e₂))`
(`exists_diff_word_short`'s state-count bound), via `autStateCard_eq_card` +
`Fintype.card_finset`/`card_prod`. -/
def subsetBoundChar (fuel c1 c2 : ℕ) : ℕ :=
  2 ^ (autStateCardFuelChar fuel c1) * 2 ^ (autStateCardFuelChar fuel c2)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- `{0,1}` gate: code `i` is a valid bit-string of length `≤ subsetBoundChar fuel c1 c2`. Screens
out both non-bit-string codes (`allBinDigitsChar`) and over-long ones (`listLenChar` vs the bound),
so the bounded-forall search below never needs the (false) converse of `codeBound_ge`. -/
def subsetGuardChar (fuel c1 c2 i : ℕ) : ℕ :=
  mulBit (allBinDigitsChar i) (isOne (1 - (listLenChar i - subsetBoundChar fuel c1 c2)))
end

section
set_option maxHeartbeats 800000 in

/-- `tabCode`'s recursion step, in the `Nat.Primrec.prec` packaging: the state is
`pair a (pair y IH)` with `a = pair B p`; it prepends `g⟨B-1-y, p⟩` onto the tail `IH`. -/
def tabStep (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (g (Nat.pair (w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) w.unpair.1.unpair.2))
    w.unpair.2.unpair.2 + 1
end

section
set_option maxHeartbeats 800000 in

/-- **Primitive-recursive tabulation.** With `a = pair B p`, `tabCode g a B` codes the list
`[g⟨0,p⟩, g⟨1,p⟩, …, g⟨B-1,p⟩]` (length `B`). Built directly from the `prec` step `tabStep`. -/
def tabCode (g : ℕ → ℕ) (a B : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => tabStep g (Nat.pair a (Nat.pair y IH))) B
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Coded list append: `decodeList (appendListCode c1 c2) = decodeList c1 ++ decodeList c2`. -/
def appendListCode (c1 c2 : ℕ) : ℕ :=
  let len1 := listLenChar c1
  let len2 := listLenChar c2
  tabCode appendListTabFn (Nat.pair (len1 + len2) (Nat.pair c1 (Nat.pair c2 len1))) (len1 + len2)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Coded list drop: `decodeList (dropCode n c) = (decodeList c).drop n`. -/
def dropCode (n c : ℕ) : ℕ :=
  let len := listLenChar c
  tabCode dropListTabFn (Nat.pair (len - n) (Nat.pair n c)) (len - n)
end

section
set_option maxHeartbeats 800000 in

/-- One fuel-recursion step, applied to every code in `[0, bound]` at once. `bodyLookup`
represents `Body`'s step with `prev` replaced by table lookup: semantically `bodyLookup (pair
table c) = Body (fun c' => nthCode table c' 0) c` (see `fuelTable_eq_of_recursion`). -/
def fuelTableStep (bodyLookup : ℕ → ℕ) (bound prevTable : ℕ) : ℕ :=
  tabCode (fun w => bodyLookup (Nat.pair w.unpair.2 w.unpair.1))
    (Nat.pair (bound + 1) prevTable) (bound + 1)
end

section
set_option maxHeartbeats 800000 in

/-- Tabulates the fuel-recursive function with base value `0` and step `bodyLookup` at every code
in `[0, bound]`, as a coded list, for `fuel` iterations. -/
def fuelTable (bodyLookup : ℕ → ℕ) (bound fuel : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1))
    (fun _ prevTable => fuelTableStep bodyLookup bound prevTable) fuel
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Tabulation lookup for `takeCode`: params `pair n c`. -/
def takeListTabFn (w : ℕ) : ℕ := nthCode (w.unpair.2.unpair.2) w.unpair.1 0
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- Coded list take: `decodeList (takeCode n c) = (decodeList c).take n`. -/
def takeCode (n c : ℕ) : ℕ :=
  let len := listLenChar c
  let B := Nat.min n len
  tabCode takeListTabFn (Nat.pair B (Nat.pair n c)) B
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- Cat-branch step for `matchesBCharBody` (`p` = `pair cutPoint (pair c cw)`). -/
def matchesBCatG (prev : ℕ → ℕ) (p : ℕ) : ℕ :=
  let i := p.unpair.1
  let c := p.unpair.2.unpair.1
  let cw := p.unpair.2.unpair.2
  mulBit (prev (Nat.pair c.unpair.2.unpair.1 (takeCode i cw)))
        (prev (Nat.pair c.unpair.2.unpair.2 (dropCode i cw)))
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- `matchesBCatG`'s step, with `prev` replaced by table lookup: `w.unpair.1` is the table,
`w.unpair.2` is the packed `pair i (pair c cw)`. -/
def matchesBCatGLookup (w : ℕ) : ℕ :=
  matchesBCatG (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- One fuel step of `matchesB` (packed subcode+word at `prev`). -/
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
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

/-- Fuel-bounded `{0,1}` mirror of `matchesB`. -/
def matchesBChar : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, c, cw =>
      matchesBCharBody (fun p => matchesBChar fuel p.unpair.1 p.unpair.2) c cw
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- `{0,1}` non-emptiness decider: bounded search over valid bit-list codes. The candidate
word's Gödel code `i` and the target `c_e` are threaded through `bExistsFn`'s own parameter slot
(`n := c_e`) rather than a fixed `0`, so `primrec_decideNonemptyBChar` composes directly out of
`primrec_bExistsFn`. -/
def decideNonemptyBChar (fuel : ℕ) (c_e : ℕ) : ℕ :=
  bExistsFn (fun p =>
      mulBit (allBinDigitsChar p.unpair.1) (matchesBChar fuel p.unpair.2 p.unpair.1))
    c_e (codeBound (autStateCardFuelChar fuel c_e))
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- `{0,1}` cap-consistency decider on Gödel codes. -/
def consistentBChar (fuel : ℕ) (c1 c2 : ℕ) : ℕ :=
  decideNonemptyBChar fuel (capCode c1 c2)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

/-- `matchesBCharBody`'s step, with `prev` replaced by table lookup. -/
def matchesBCharBodyLookup (w : ℕ) : ℕ :=
  matchesBCharBody (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2.unpair.1 w.unpair.2.unpair.2
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

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
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

@[irreducible] def interEqChar (fuel c1 c2 : ℕ) : ℕ :=
  mulBit (subsetBChar fuel c1 c2) (subsetBChar fuel c2 c1)
end

section
/-- `n.unpair.2 ≤ n` (choice-free); the decreasing measure for `decodeList`. -/
theorem unpair_snd_le (n : ℕ) : n.unpair.2 ≤ n := by
  have h := le_pair_right n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h
end

section
/-- Decode a natural back into a list of naturals, inverting `encodeList`. Well-founded on the
remaining code (`c.unpair.2 ≤ c < c + 1`). -/
def decodeList : ℕ → List ℕ
  | 0 => []
  | (c + 1) => c.unpair.1 :: decodeList c.unpair.2
decreasing_by exact Nat.lt_succ_of_le (unpair_snd_le c)
end

section
set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 800000 in

set_option maxHeartbeats 800000 in

def c9b6_decodeListBool (c : ℕ) : List Bool :=
  (decodeList c).map fun n => decide (n = 1)
end

section
/-- `id` is primitive recursive (choice-free). -/
theorem primrec_id : Nat.Primrec id :=
  (Nat.Primrec.left.pair Nat.Primrec.right).of_eq fun n => pair_unpair n

/-- The `prec` recursor for addition computes the sum. -/
theorem rec_add (a b : ℕ) : Nat.rec a (fun _ IH => IH + 1) b = a + b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH + 1) k + 1 = a + (k + 1); omega

/-- The `prec` recursor for multiplication computes the product. -/
private theorem rec_mul (a b : ℕ) : Nat.rec 0 (fun _ IH => a + IH) b = a * b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    show a + Nat.rec 0 (fun _ IH => a + IH) k = a * (k + 1)
    rw [Nat.mul_succ]; omega

/-- Addition is primitive recursive (choice-free). -/
theorem primrec_add : Nat.Primrec (Nat.unpaired (· + ·)) :=
  (Nat.Primrec.prec primrec_id
      ((Nat.Primrec.succ.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_add _ _

/-- Multiplication is primitive recursive (choice-free). -/
theorem primrec_mul : Nat.Primrec (Nat.unpaired (· * ·)) :=
  (Nat.Primrec.prec Nat.Primrec.zero
      (primrec_add.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.right.comp Nat.Primrec.right)))).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd, Nat.unpaired]
    exact rec_mul _ _

/-- The `prec` recursor for predecessor computes `n - 1`. -/
private theorem rec_pred (n : ℕ) : Nat.rec 0 (fun y _ => y) n = n - 1 := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- Predecessor `n ↦ n - 1` is primitive recursive (choice-free; mathlib's `Nat.Primrec.pred` is
classical). -/
theorem primrec_pred : Nat.Primrec (fun n => n - 1) :=
  ((Nat.Primrec.prec Nat.Primrec.zero (Nat.Primrec.left.comp Nat.Primrec.right)).comp
    (primrec_id.pair primrec_id)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    exact rec_pred n

/-- The `prec` recursor for truncated subtraction computes `a - b`. -/
private theorem rec_sub (a b : ℕ) : Nat.rec a (fun _ IH => IH - 1) b = a - b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH - 1) k - 1 = a - (k + 1); rw [ih]; omega

/-- Truncated subtraction is primitive recursive (choice-free; mathlib's `Nat.Primrec.sub` is
classical). -/
theorem primrec_sub : Nat.Primrec (Nat.unpaired (· - ·)) :=
  (Nat.Primrec.prec primrec_id
    ((primrec_pred.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_sub _ _

/-- `a * b = 1 ↔ a = 1 ∧ b = 1` over `ℕ` (choice-free; avoids the classical generic `mul_eq_one`). -/
theorem nat_mul_eq_one {a b : ℕ} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h => ⟨Nat.dvd_one.mp ⟨b, h.symm⟩, Nat.dvd_one.mp ⟨a, ?_⟩⟩, fun h => by rw [h.1, h.2]⟩
  rw [Nat.mul_comm] at h; exact h.symm

/-- `fun n => f n + g n` is primitive recursive. -/
theorem primrec_add₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n + g n) :=
  (primrec_add.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n * g n` is primitive recursive. -/
theorem primrec_mul₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n * g n) :=
  (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n - g n` (truncated) is primitive recursive. -/
theorem primrec_sub₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n - g n) :=
  (primrec_sub.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]


/-- `selectFn` of primitive-recursive `c, a, b` is primitive recursive. -/
theorem primrec_selectFn {c a b : ℕ → ℕ} (hc : Nat.Primrec c) (ha : Nat.Primrec a)
    (hb : Nat.Primrec b) : Nat.Primrec (fun n => selectFn (c n) (a n) (b n)) :=
  primrec_add₂ (primrec_mul₂ hc ha) (primrec_mul₂ (primrec_sub₂ (Nat.Primrec.const 1) hc) hb)


/-- Recursive decidability transfers across a pointwise logical equivalence. -/
theorem RecDecidable.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : RecDecidable p) :
    RecDecidable q := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨f, hf, fun n => (h n).trans (hfe n)⟩

/-- **Reindexing.** If `p` is recursively decidable and `g` is primitive recursive, then
`fun n => p (g n)` is recursively decidable. -/
theorem RecDecidable.comp {p : ℕ → Prop} (hp : RecDecidable p) {g : ℕ → ℕ}
    (hg : Nat.Primrec g) : RecDecidable (fun n => p (g n)) := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨fun n => f (g n), hf.comp hg, fun n => hfe (g n)⟩

/-- **Conjunction.** Recursive decidability is closed under `∧` (multiply the `{0,1}` deciders). -/
theorem RecDecidable.and {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∧ q n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  obtain ⟨g, hg, hge⟩ := hq
  refine ⟨fun n => f n * g n, ?_, fun n => ?_⟩
  · exact (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
      simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  · rw [nat_mul_eq_one]; exact and_congr (hfe n) (hge n)

/-- **Equality of two primitive-recursive functions is recursively decidable.** The `{0,1}`-valued
characteristic function is `1 - ((a t - b t) + (b t - a t))` (truncated subtraction), which is `1`
exactly when `a t = b t`; primitive recursive via `primrec_sub`/`primrec_add`, and the biconditional
is `omega` (which understands truncated subtraction). -/
theorem RecDecidable.natEq {a b : ℕ → ℕ} (ha : Nat.Primrec a) (hb : Nat.Primrec b) :
    RecDecidable (fun t => a t = b t) := by
  refine ⟨fun t => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· + ·)
      (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (a t) (b t)))
        (Nat.unpaired (· - ·) (Nat.pair (b t) (a t)))))), ?_, fun t => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_add.comp
      ((primrec_sub.comp (ha.pair hb)).pair (primrec_sub.comp (hb.pair ha)))))
  · simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- **Negation.** Recursive decidability is closed under `¬` (negate the `{0,1}` decider). -/
theorem RecDecidable.not {p : ℕ → Prop} (hp : RecDecidable p) : RecDecidable (fun n => ¬ p n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  refine ⟨fun n => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· - ·) (Nat.pair 1
      (Nat.unpaired (· + ·) (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (f n) 1))
        (Nat.unpaired (· - ·) (Nat.pair 1 (f n)))))))), ?_, fun n => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_sub.comp
      ((Nat.Primrec.const 1).pair (primrec_add.comp
        ((primrec_sub.comp (hf.pair (Nat.Primrec.const 1))).pair
          (primrec_sub.comp ((Nat.Primrec.const 1).pair hf)))))))
  · show ¬ p n ↔ _
    rw [hfe n]
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- Every recursively decidable predicate is **decidable** (the decider is `f n = 1`, decidable
equality on `ℕ`); useful for choice-free De Morgan. -/
theorem RecDecidable.em {p : ℕ → Prop} (hp : RecDecidable p) (n : ℕ) : p n ∨ ¬ p n := by
  obtain ⟨f, _, hfe⟩ := hp
  by_cases h : f n = 1
  · exact Or.inl ((hfe n).mpr h)
  · exact Or.inr (fun hp => h ((hfe n).mp hp))

/-- **Disjunction.** Recursive decidability is closed under `∨`, via choice-free De Morgan
`p ∨ q ↔ ¬(¬p ∧ ¬q)` (the non-constructive direction uses `RecDecidable.em`). -/
theorem RecDecidable.or {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∨ q n) := by
  refine RecDecidable.of_iff (fun n => ?_) (hp.not.and hq.not).not
  constructor
  · rintro (h | h) ⟨hnp, hnq⟩
    · exact hnp h
    · exact hnq h
  · intro h
    rcases hp.em n with hp' | hp'
    · exact Or.inl hp'
    · rcases hq.em n with hq' | hq'
      · exact Or.inr hq'
      · exact absurd ⟨hp', hq'⟩ h


/-- **Every recursively decidable predicate is recursively enumerable.** Use the decider as the
relation `q ⟨i, n⟩ := p n` (a reindex of `p` along `unpair.2`, dropping the search variable `i`); the
witness `i = 0` makes the projection trivial. -/
theorem RecDecidable.re {p : ℕ → Prop} (hp : RecDecidable p) : REPred p := by
  refine ⟨fun t => p t.unpair.2, hp.comp Nat.Primrec.right, fun n => ?_⟩
  simp only [unpair_pair_snd]
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

/-- A recursively decidable binary relation is recursively enumerable. -/
theorem RecDecidable₂.re {r : ℕ → ℕ → Prop} (hr : RecDecidable₂ r) : REPred₂ r :=
  RecDecidable.re hr

/-- Recursive enumerability transfers across a pointwise logical equivalence. -/
theorem REPred.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : REPred p) : REPred q := by
  obtain ⟨r, hr, hre⟩ := hp
  exact ⟨r, hr, fun n => (h n).trans (hre n)⟩

/-- **Reindexing.** If `p` is r.e. and `g` is primitive recursive, then `fun n => p (g n)` is r.e.
(absorb `g` into the decidable relation along `unpair.2`). -/
theorem REPred.comp {p : ℕ → Prop} (hp : REPred p) {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    REPred (fun n => p (g n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun t => q (Nat.pair t.unpair.1 (g t.unpair.2)),
    hq.comp (Nat.Primrec.left.pair (hg.comp Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact hqe (g n)

/-- **Conjunction.** Recursive enumerability is closed under `∧`: combine the two decidable relations
and run the two searches in parallel (pairing the search variables `i, j` into a single `w`). -/
theorem REPred.and {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∧ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => a (Nat.pair u.unpair.1.unpair.1 u.unpair.2)
      ∧ b (Nat.pair u.unpair.1.unpair.2 u.unpair.2),
    (ha.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)).and
      (hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hae n, hbe n]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pair i j, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hi, hj⟩⟩
  · rintro ⟨w, hw1, hw2⟩
    exact ⟨⟨w.unpair.1, hw1⟩, ⟨w.unpair.2, hw2⟩⟩

/-- **Existential projection.** If `p` is r.e. then so is `fun n => ∃ i, p ⟨i, n⟩`: fold the new
existential variable `i` into the search variable (pairing it with the decidable relation's own
search variable `j`). -/
theorem REPred.proj {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun n => ∃ i, p (Nat.pair i n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun u => q (Nat.pair u.unpair.1.unpair.2 (Nat.pair u.unpair.1.unpair.1 u.unpair.2)),
    hq.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
      ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨i, hi⟩
    rw [hqe (Nat.pair i n)] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨Nat.pair i j, by simpa only [unpair_pair_fst, unpair_pair_snd] using hj⟩
  · rintro ⟨w, hw⟩
    refine ⟨w.unpair.1, ?_⟩
    rw [hqe (Nat.pair w.unpair.1 n)]
    exact ⟨w.unpair.2, hw⟩

/-- **Disjunction of r.e. predicates is r.e.** A witness `w` carries a tag `w.1 ∈ {0,1}` selecting
which disjunct's search index `w.2` to use; the underlying relation is recursively decidable by
`RecDecidable.or`/`.and`/`.natEq`. (Used for the sum-mapping `f + g` of Theorem 7.4.) -/
theorem REPred.or {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∨ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => (a (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 0)
      ∨ (b (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 1), ?_, fun n => ?_⟩
  · refine RecDecidable.or (RecDecidable.and ?_ ?_) (RecDecidable.and ?_ ?_)
    · exact ha.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
    · exact hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  · show p n ∨ q n ↔ _
    rw [hae n, hbe n]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · refine ⟨Nat.pair 0 i, Or.inl ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
      · refine ⟨Nat.pair 1 i, Or.inr ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
    · rintro ⟨w, hw⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hw
      rcases hw with ⟨hi, _⟩ | ⟨hi, _⟩
      · exact Or.inl ⟨w.unpair.2, hi⟩
      · exact Or.inr ⟨w.unpair.2, hi⟩


/-- `a ≤ pair a b` (choice-free). -/
theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair
  split <;> omega


/-- The length of a list is bounded by its code; this is the fuel bound that lets a `c`-fold iterate
enough times to consume the whole list coded by `c`. -/
theorem encodeList_length_le : ∀ l : List ℕ, l.length ≤ encodeList l
  | [] => Nat.le_refl 0
  | a :: l => by
    simp only [encodeList, List.length_cons]
    have hrec := encodeList_length_le l
    have hle : encodeList l ≤ Nat.pair a (encodeList l) := le_pair_right a (encodeList l)
    omega


/-- Empty remaining code: the fold state is unchanged. -/
theorem foldStep_zero (stp : ℕ → ℕ) (params acc : ℕ) :
    foldStep stp params (Nat.pair 0 acc) = Nat.pair 0 acc := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

/-- Nonempty remaining code `pair a t + 1`: pop `a`, recurse on `t`, update the accumulator. -/
theorem foldStep_pos (stp : ℕ → ℕ) (params a t acc : ℕ) :
    foldStep stp params (Nat.pair (Nat.pair a t + 1) acc)
      = Nat.pair t (stp (Nat.pair a (Nat.pair acc params))) := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  have h1 : 1 - (Nat.pair a t + 1) = 0 := by omega
  have h2 : Nat.pair a t + 1 - 1 = Nat.pair a t := by omega
  rw [h1, h2, selectFn_zero, unpair_pair_fst, unpair_pair_snd]


/-- `Nat.rec` with a counter-independent step is just function iteration (choice-free). Needed to
bridge the `Nat.Primrec.prec` form (a `Nat.rec`) with `foldCode`'s `Function.iterate` form. -/
theorem rec_const_iterate (f : ℕ → ℕ) (s : ℕ) :
    ∀ k : ℕ, Nat.rec (motive := fun _ => ℕ) s (fun _ ih => f ih) k = f^[k] s
  | 0 => rfl
  | (k + 1) => by
      rw [Function.iterate_succ_apply']
      exact congrArg f (rec_const_iterate f s k)

/-- Core correctness of the iteration: starting from `pair (encodeList l) acc`, after at least
`l.length` steps the accumulator equals the `List.foldl` of the step over `l`. -/
theorem foldStep_iterate (stp : ℕ → ℕ) (params : ℕ) :
    ∀ (k : ℕ) (l : List ℕ) (acc : ℕ), l.length ≤ k →
      ((foldStep stp params)^[k] (Nat.pair (encodeList l) acc)).unpair.2
        = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) acc l := by
  intro k
  induction k with
  | zero =>
    intro l acc hlen
    cases l with
    | nil => simp only [Function.iterate_zero_apply, encodeList, unpair_pair_snd, List.foldl_nil]
    | cons a l' => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    intro l acc hlen
    rw [Function.iterate_succ_apply]
    cases l with
    | nil =>
      rw [show encodeList ([] : List ℕ) = 0 from rfl, foldStep_zero]
      exact ih [] acc (Nat.zero_le k)
    | cons a l' =>
      have hlen' : l'.length ≤ k := by simp only [List.length_cons] at hlen; omega
      rw [show encodeList (a :: l') = Nat.pair a (encodeList l') + 1 from rfl, foldStep_pos,
        ih l' (stp (Nat.pair a (Nat.pair acc params))) hlen', List.foldl_cons]

/-- **Correctness of `foldCode`.** Folding the code of `l` equals the corresponding `List.foldl`. -/
theorem foldCode_eq (stp : ℕ → ℕ) (params z : ℕ) (l : List ℕ) :
    foldCode stp params z (encodeList l)
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z l := by
  unfold foldCode
  exact foldStep_iterate stp params (encodeList l) l z (encodeList_length_le l)


theorem unpair_left_le (n : ℕ) : n.unpair.1 ≤ n := by
  have h := le_pair_left n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

/-- Weak version of mathlib's `Nat.pair_lt_pair_left`. -/
theorem pair_le_pair_left (b : ℕ) {a a' : ℕ} (h : a ≤ a') : Nat.pair a b ≤ Nat.pair a' b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (Nat.pair_lt_pair_left b hlt)

/-- Weak version of mathlib's `Nat.pair_lt_pair_right`. -/
theorem pair_le_pair_right' (a : ℕ) {b b' : ℕ} (h : b ≤ b') : Nat.pair a b ≤ Nat.pair a b' := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (Nat.pair_lt_pair_right a hlt)

/-- `Nat.pair` is weakly monotone in both arguments jointly. -/
theorem pair_le_pair {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' :=
  le_trans (pair_le_pair_left b ha) (pair_le_pair_right' a' hb)


theorem decodeList_zero : decodeList 0 = [] := by rw [decodeList]

theorem decodeList_succ (c : ℕ) :
    decodeList (c + 1) = c.unpair.1 :: decodeList c.unpair.2 := by
  rw [decodeList]

/-- `encodeList ∘ decodeList = id`: every natural is the code of its decoded list. -/
theorem encodeList_decodeList (c : ℕ) : encodeList (decodeList c) = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp only [decodeList_zero, encodeList]
    | succ d =>
      rw [decodeList_succ, encodeList, ih d.unpair.2 (Nat.lt_succ_of_le (unpair_snd_le d)),
        pair_unpair]

/-- **Correctness of `foldCode` on an arbitrary code.** `foldCode` over any natural `c` equals the
`List.foldl` over the list `c` decodes to. -/
theorem foldCode_eq' (stp : ℕ → ℕ) (params z c : ℕ) :
    foldCode stp params z c
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z (decodeList c) := by
  conv_lhs => rw [← encodeList_decodeList c]
  rw [foldCode_eq]

/-- `foldStep` (with the parameter packed into the state as `pair params state`) is primitive
recursive whenever the step `stp` is. This is the workhorse for `primrec_foldCode`. -/
theorem primrec_foldStepPacked {stp : ℕ → ℕ} (hstp : Nat.Primrec stp) :
    Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) := by
  have hparams : Nat.Primrec (fun w => w.unpair.1) := Nat.Primrec.left
  have hstate : Nat.Primrec (fun w => w.unpair.2) := Nat.Primrec.right
  have hrc : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hcond : Nat.Primrec (fun w => 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.const 1) hrc
  have hrcm1 : Nat.Primrec (fun w => w.unpair.2.unpair.1 - 1) :=
    primrec_sub₂ hrc (Nat.Primrec.const 1)
  have hhead : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hrcm1
  have htail : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hrcm1
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2 w.unpair.1) := hacc.pair hparams
  have harg : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) := hhead.pair hinner
  have hstpv : Nat.Primrec
      (fun w => stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1))) := hstp.comp harg
  have helse : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.2
        (stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
          (Nat.pair w.unpair.2.unpair.2 w.unpair.1)))) := htail.pair hstpv
  exact (primrec_selectFn hcond hstate helse).of_eq fun _ => rfl

/-- **`foldCode` is primitive recursive** in all of its (primitive-recursive) inputs. -/
theorem primrec_foldCode {stp : ℕ → ℕ} (hstp : Nat.Primrec stp)
    {params z c : ℕ → ℕ} (hp : Nat.Primrec params) (hz : Nat.Primrec z) (hc : Nat.Primrec c) :
    Nat.Primrec (fun n => foldCode stp (params n) (z n) (c n)) := by
  have hfoldw : Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) :=
    primrec_foldStepPacked hstp
  have hg : Nat.Primrec (fun x => foldStep stp x.unpair.1.unpair.1 x.unpair.2.unpair.2) :=
    (hfoldw.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun _ => by
        simp only [unpair_pair_fst, unpair_pair_snd]
  have hprec := Nat.Primrec.prec Nat.Primrec.right hg
  refine (Nat.Primrec.right.comp
    (hprec.comp ((hp.pair (hc.pair hz)).pair hc))).of_eq fun n => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rw [rec_const_iterate]
  rfl


theorem isOne_le_one (v : ℕ) : isOne v ≤ 1 := by unfold isOne; omega


theorem isOne_of_ne_one {v : ℕ} (h : v ≠ 1) : isOne v = 0 := by
  unfold isOne
  omega

theorem primrec_isOne : Nat.Primrec isOne :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const 1))
      (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))


theorem isZero_eq_one_iff (n : ℕ) : isZero n = 1 ↔ n = 0 := by
  unfold isZero; omega

theorem isZero_le_one (n : ℕ) : isZero n ≤ 1 := by unfold isZero; omega

theorem primrec_isZero : Nat.Primrec isZero := by
  have hmin : Nat.Primrec (fun n => min n 1) :=
    (primrec_sub₂ primrec_id (primrec_sub₂ primrec_id (Nat.Primrec.const 1))).of_eq fun n => by
      rcases n with _ | n
      · rfl
      · show n + 1 - (n + 1 - 1) = min (n + 1) 1
        rw [Nat.min_eq_right (Nat.le_add_left 1 n)]
        omega
  exact primrec_sub₂ (Nat.Primrec.const 1) hmin

/-- `{0,1}` test for `f n ≤ g n` (truncated subtraction). -/
theorem primrec_le {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => isZero (f n - g n)) :=
  primrec_isZero.comp (primrec_sub₂ hf hg)


theorem bForallFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bForallFn g n N ≤ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ N ih =>
    show selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 ≤ 1
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]; exact Nat.zero_le 1
    · rw [h, selectFn_one]; exact isOne_le_one _

theorem bForallFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bForallFn g n N = 1 ↔ ∀ i, i < N → g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    constructor
    · intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _; rfl
  | succ N ih =>
    have hstep : bForallFn g n (N + 1)
        = selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 := rfl
    have hle := bForallFn_le_one g n N
    rw [hstep]
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero]
      constructor
      · intro hcontra; exact absurd hcontra (by decide)
      · intro hall
        have hb : bForallFn g n N = 1 := ih.mpr (fun i hi => hall i (Nat.lt_succ_of_lt hi))
        rw [h0] at hb; exact hb
    · rw [h1, selectFn_one, isOne_eq_one_iff]
      constructor
      · intro hgN i hi
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · exact (ih.mp h1) i hlt
        · subst heq; exact hgN
      · intro hall; exact hall N (Nat.lt_succ_self N)


theorem bExistsFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bExistsFn g n N ≤ 1 := by
  induction N with
  | zero => simp [bExistsFn]
  | succ N ih =>
    show selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) ≤ 1
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]
      exact isOne_le_one _
    · rw [h, selectFn_one]

/-- `bExistsFn` only depends on `g` through its values on the search range `{pair i n | i < N}`. -/
theorem bExistsFn_congr {g1 g2 : ℕ → ℕ} {n N : ℕ}
    (h : ∀ i < N, g1 (Nat.pair i n) = g2 (Nat.pair i n)) : bExistsFn g1 n N = bExistsFn g2 n N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show selectFn (bExistsFn g1 n N) 1 (isOne (g1 (Nat.pair N n)))
      = selectFn (bExistsFn g2 n N) 1 (isOne (g2 (Nat.pair N n)))
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h N (Nat.lt_succ_self N)]

theorem bExistsFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bExistsFn g n N = 1 ↔ ∃ i, i < N ∧ g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    simp [bExistsFn]
  | succ N ih =>
    have hstep : bExistsFn g n (N + 1)
        = selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) := rfl
    rw [hstep]
    have hle := bExistsFn_le_one g n N
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero, isOne_eq_one_iff]
      constructor
      · intro hgN; exact ⟨N, Nat.lt_succ_self N, hgN⟩
      · intro ⟨i, hi, hg⟩
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · have hne : bExistsFn g n N = 1 := ih.mpr ⟨i, hlt, hg⟩
          omega
        · subst heq; exact hg
    · rw [h1, selectFn_one]
      constructor
      · intro _
        obtain ⟨i, hi, hg⟩ := ih.mp h1
        exact ⟨i, Nat.lt_succ_of_lt hi, hg⟩
      · intro _; rfl

theorem primrec_bExistsFn {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bExistsFn g t.unpair.1 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2 1 (isOne (g (Nat.pair w.unpair.2.unpair.1 w.unpair.1)))) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.const 1)
      (primrec_isOne.comp (hg.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-- Parametrized variant of `primrec_bExistsFn`: `g` may also depend on an external `param`
(e.g. `fuel`) held fixed throughout the search, packed as `t.unpair.1.unpair.1`. Needed once `g`
itself is only jointly (not per-fixed-`param`) primitive recursive. -/
theorem primrec_bExistsFn_param {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bExistsFn (fun p => g (Nat.pair t.unpair.1.unpair.1 p))
      t.unpair.1.unpair.2 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2 1
        (isOne (g (Nat.pair w.unpair.1.unpair.1
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))))) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.const 1)
      (primrec_isOne.comp (hg.comp
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
          (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
            (Nat.Primrec.right.comp Nat.Primrec.left)))))
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-- `decodeList ∘ encodeList = id` (the round-trip the other way from `encodeList_decodeList`). -/
theorem decodeList_encodeList : ∀ l : List ℕ, decodeList (encodeList l) = l
  | [] => by rw [encodeList, decodeList_zero]
  | a :: l => by
    rw [encodeList, decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_encodeList l]


theorem reForallStp_eq (qc : ℕ → ℕ) (acc x : ℕ) :
    reForallStp qc (Nat.pair x (Nat.pair acc 0)) = reForallF qc acc x := by
  unfold reForallStp reForallF
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem reForallChar_eq (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c
      = (List.foldl (reForallF qc) (Nat.pair w 1) (decodeList c)).unpair.2 := by
  have hfun : (fun (acc x : ℕ) => reForallStp qc (Nat.pair x (Nat.pair acc 0))) = reForallF qc := by
    funext acc x; exact reForallStp_eq qc acc x
  unfold reForallChar
  rw [foldCode_eq', hfun]

/-- **Core induction.** Threading witness code `w` through `l`, the final flag is `1` iff the start
flag was `1` and, position by position, the `k`-th witness of `decodeList w` satisfies `qc`. -/
theorem reForallF_foldl_eq_one_iff (qc : ℕ → ℕ) :
    ∀ (l : List ℕ) (w flag : ℕ), flag ≤ 1 →
      ((List.foldl (reForallF qc) (Nat.pair w flag) l).unpair.2 = 1 ↔
        flag = 1 ∧ ∀ k, k < l.length →
          qc (Nat.pair ((decodeList w).getD k 0) (l.getD k 0)) = 1) := by
  intro l
  induction l with
  | nil =>
    intro w flag _
    simp only [List.foldl_nil, unpair_pair_snd, List.length_nil, Nat.not_lt_zero,
      false_implies, implies_true, and_true]
  | cons x l ih =>
    intro w flag hflag
    have hi : (decodeList w).getD 0 0 = (w - 1).unpair.1 := by
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.1 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.fst Nat.unpair_zero
        rw [decodeList_zero, List.getD_nil, hz]
      · rw [decodeList_succ, List.getD_cons_zero, Nat.add_sub_cancel]
    have htail : ∀ k, (decodeList w).getD (k + 1) 0 = (decodeList (w - 1).unpair.2).getD k 0 := by
      intro k
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.2 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.snd Nat.unpair_zero
        rw [decodeList_zero, hz, decodeList_zero, List.getD_nil, List.getD_nil]
      · rw [decodeList_succ, List.getD_cons_succ, Nat.add_sub_cancel]
    have hstep : List.foldl (reForallF qc) (Nat.pair w flag) (x :: l)
        = List.foldl (reForallF qc) (Nat.pair (w - 1).unpair.2
            (selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0)) l := by
      rw [List.foldl_cons]
      congr 1
      show reForallF qc (Nat.pair w flag) x = _
      unfold reForallF
      rw [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set flag' := selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0 with hflag'def
    have hflag'le : flag' ≤ 1 := by
      rw [hflag'def]
      rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih (w - 1).unpair.2 flag' hflag'le]
    constructor
    · rintro ⟨hf', hrest⟩
      have hsplit : flag = 1 ∧ qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        rw [hflag'def] at hf'
        rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hf'; exact absurd hf' (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hf'; exact ⟨h, hf'⟩
      refine ⟨hsplit.1, fun k hk => ?_⟩
      rcases k with _ | k'
      · rw [List.getD_cons_zero, hi]; exact hsplit.2
      · rw [List.getD_cons_succ, htail]
        exact hrest k' (by simp only [List.length_cons] at hk; omega)
    · rintro ⟨hflag1, hall⟩
      have hhead : qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        have := hall 0 (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_zero, hi] at this
      refine ⟨?_, fun k hk => ?_⟩
      · rw [hflag'def, hflag1, selectFn_one, isOne_eq_one_iff]; exact hhead
      · have := hall (k + 1) (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_succ, htail] at this

theorem reForallChar_eq_one_iff (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c = 1 ↔
      ∀ k, k < (decodeList c).length →
        qc (Nat.pair ((decodeList w).getD k 0) ((decodeList c).getD k 0)) = 1 := by
  rw [reForallChar_eq, reForallF_foldl_eq_one_iff qc (decodeList c) w 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem primrec_reForallStp {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (reForallStp qc) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrw : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hpm : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1 - 1) :=
    primrec_sub₂ hrw (Nat.Primrec.const 1)
  have hi : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hpm
  have hrw' : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hpm
  have hcall : Nat.Primrec (fun w : ℕ =>
      qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1)) :=
    hqc.comp (hi.pair hx)
  have hB : Nat.Primrec (fun w : ℕ =>
      selectFn w.unpair.2.unpair.1.unpair.2
        (isOne (qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp hcall) (Nat.Primrec.const 0)
  exact (hrw'.pair hB).of_eq (fun _ => rfl)

theorem primrec_reForallChar {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (fun t => reForallChar qc t.unpair.1 t.unpair.2) := by
  have hfold := primrec_foldCode (primrec_reForallStp hqc) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair (Nat.Primrec.const 1)) Nat.Primrec.right
  exact (Nat.Primrec.right.comp hfold).of_eq (fun _ => rfl)

/-- **Bounded `∀` over a coded list preserves recursive enumerability.** If `p` is r.e. then so is
`fun c => ∀ e ∈ decodeList c, p e`: the finite tuple of per-entry witnesses is packed into a single
search code `w`, and the `{0,1}` flag `reForallChar` makes the body recursively decidable. -/
theorem REPred.forall_mem_decodeList {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun c => ∀ e ∈ decodeList c, p e) := by
  obtain ⟨q, hq, hqe⟩ := hp
  obtain ⟨qc, hqcp, hqcs⟩ := hq
  -- per-entry: `p e ↔ ∃ j, qc ⟨j, e⟩ = 1`
  have hpe : ∀ e, p e ↔ ∃ j, qc (Nat.pair j e) = 1 := by
    intro e; rw [hqe e]; exact exists_congr (fun j => hqcs (Nat.pair j e))
  -- membership gives an index whose `getD` recovers the element
  have hmemgetD : ∀ (l : List ℕ) (e : ℕ), e ∈ l → ∃ k, k < l.length ∧ l.getD k 0 = e := by
    intro l
    induction l with
    | nil => intro e he; cases he
    | cons a l ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨0, by simp only [List.length_cons]; omega, by rw [List.getD_cons_zero]⟩
      · obtain ⟨k, hk, hek⟩ := ih e he'
        exact ⟨k + 1, by simp only [List.length_cons]; omega, by rw [List.getD_cons_succ]; exact hek⟩
  refine ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2 = 1,
    ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2, primrec_reForallChar hqcp,
      fun _ => Iff.rfl⟩, fun c => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · intro hall
    -- build a witness list for `decodeList c`
    have hwit : ∀ (l : List ℕ), (∀ e ∈ l, ∃ j, qc (Nat.pair j e) = 1) →
        ∃ iws : List ℕ, ∀ k, k < l.length →
          qc (Nat.pair (iws.getD k 0) (l.getD k 0)) = 1 := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | cons e l ih =>
        intro hh
        obtain ⟨j, hj⟩ := hh e (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨iws, hiws⟩ := ih (fun e' he' => hh e' (List.mem_cons.mpr (Or.inr he')))
        refine ⟨j :: iws, fun k hk => ?_⟩
        rcases k with _ | k'
        · rw [List.getD_cons_zero, List.getD_cons_zero]; exact hj
        · rw [List.getD_cons_succ, List.getD_cons_succ]
          exact hiws k' (by simp only [List.length_cons] at hk; omega)
    obtain ⟨iws, hiws⟩ := hwit (decodeList c) (fun e he => (hpe e).mp (hall e he))
    refine ⟨encodeList iws, (reForallChar_eq_one_iff qc _ c).mpr (fun k hk => ?_)⟩
    rw [decodeList_encodeList]; exact hiws k hk
  · rintro ⟨w, hw⟩
    rw [reForallChar_eq_one_iff] at hw
    intro e he
    obtain ⟨k, hk, hek⟩ := hmemgetD (decodeList c) e he
    rw [hpe e]
    refine ⟨(decodeList w).getD k 0, ?_⟩
    have := hw k hk
    rwa [hek] at this


/-- `lowOr x y = (x ||| y) % 2`: both sides depend only on the low bits `x % 2`, `y % 2`. -/
theorem lowOr_eq_mod (x y : ℕ) : lowOr x y = (x ||| y) % 2 := by
  have key : ((x ||| y) % 2 = 1) ↔ (x % 2 = 1 ∨ y % 2 = 1) := by
    have hb := Nat.testBit_lor x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_or]
  have e1 : (x ||| y) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold lowOr
  -- explicit case split avoids feeding `omega` an `↔`/disjunction (which pulls `Classical.choice`)
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · -- x%2=0, y%2=0 : `(x|||y)%2 ≠ 1`
    have hne : (x ||| y) % 2 ≠ 1 := fun h => by rcases key.mp h with h' | h' <;> omega
    omega
  · -- x%2=0, y%2=1
    rw [key.mpr (Or.inr hy)]
  · -- x%2=1, y%2=0
    rw [key.mpr (Or.inl hx)]
  · -- x%2=1, y%2=1
    rw [key.mpr (Or.inl hx)]


/-- One recursion step for `Nat.lor` on the low bit: `x ||| y = 2 (x/2 ||| y/2) + lowOr x y`. -/
theorem lor_low_rec (x y : ℕ) : x ||| y = 2 * (x / 2 ||| y / 2) + lowOr x y := by
  have hdiv : (x ||| y) / 2 = x / 2 ||| y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowOr_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ||| y) 2]
  rw [hdiv, hmod]

/-- **Invariant of the bitwise-OR iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k ||| b/2^k) = a ||| b`. -/
theorem lorStep_iter_spec (a b : ℕ) : ∀ k,
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k ||| b / 2 ^ k) = a ||| b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    -- compute the four projections of one `lorStep`
    have p11 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowOr (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, lor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

/-- **Correctness of the iterative bitwise OR.** `myLor a b = a ||| b`. -/
theorem myLor_eq_lor (a b : ℕ) : myLor a b = a ||| b := by
  unfold myLor
  obtain ⟨_, _, _, hAcc⟩ := lorStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc


theorem allListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    allListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc (isOne (g (Nat.pair x p))) 0 := by
  unfold allListStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem allListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c
      = List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) 1 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => allListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) := by
    funext acc x; exact allListStp_eq g acc x p
  unfold allListChar; rw [foldCode_eq', hfun]

/-- Core induction for the AND-fold: starting from `acc ≤ 1`, the fold is `1` iff `acc = 1` and every
list entry passes the decider `g`. -/
theorem allList_foldl_eq_one_iff (g : ℕ → ℕ) (p : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
      (List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) acc l = 1 ↔
        acc = 1 ∧ ∀ x ∈ l, g (Nat.pair x p) = 1) := by
  intro l
  induction l with
  | nil => intro acc _; simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true,
      and_true]
  | cons x l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    set acc' := selectFn acc (isOne (g (Nat.pair x p))) 0 with hacc'
    have hacc'le : acc' ≤ 1 := by
      rw [hacc']
      rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih acc' hacc'le]
    constructor
    · rintro ⟨hacc'1, hrest⟩
      have hsplit : acc = 1 ∧ g (Nat.pair x p) = 1 := by
        rw [hacc'] at hacc'1
        rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hacc'1; exact absurd hacc'1 (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hacc'1; exact ⟨h, hacc'1⟩
      refine ⟨hsplit.1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hsplit.2
      · exact hrest y hy'
    · rintro ⟨hacc1, hall⟩
      have hhead : g (Nat.pair x p) = 1 := hall x (List.mem_cons.mpr (Or.inl rfl))
      refine ⟨?_, fun y hy => hall y (List.mem_cons.mpr (Or.inr hy))⟩
      rw [hacc', hacc1, selectFn_one, isOne_eq_one_iff]; exact hhead

theorem allListChar_eq_one_iff (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c = 1 ↔ ∀ x ∈ decodeList c, g (Nat.pair x p) = 1 := by
  rw [allListChar_eq, allList_foldl_eq_one_iff g p (decodeList c) 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem allListChar_le_one (g : ℕ → ℕ) (p c : ℕ) : allListChar g p c ≤ 1 := by
  have h : ∀ (l : List ℕ) (z : ℕ), z ≤ 1 →
      List.foldl (fun acc x => allListStp g (Nat.pair x (Nat.pair acc p))) z l ≤ 1 := by
    intro l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons x xs ih =>
      intro z hz
      simp only [List.foldl_cons]
      apply ih
      rw [allListStp_eq]
      rcases (show z = 0 ∨ z = 1 by omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact Nat.zero_le 1
      · rw [h1, selectFn_one]; exact isOne_le_one _
  unfold allListChar
  rw [foldCode_eq']
  exact h (decodeList c) 1 (le_refl 1)

theorem primrec_allListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (allListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc hcall (Nat.Primrec.const 0)).of_eq fun _ => rfl


theorem isBinDigit_eq_one_iff (n : ℕ) : isBinDigit n = 1 ↔ n = 0 ∨ n = 1 := by
  unfold isBinDigit selectFn isOne
  match n with | 0 | 1 => simp | n + 2 => simp

theorem primrec_isBinDigit : Nat.Primrec isBinDigit := by
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) primrec_id)
  refine (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 (Nat.Primrec.const 1) (Nat.Primrec.const 0))).of_eq fun _ => rfl


theorem allBinDigitsChar_eq_one_iff (c : ℕ) :
    allBinDigitsChar c = 1 ↔ ∀ x ∈ decodeList c, x = 0 ∨ x = 1 := by
  unfold allBinDigitsChar
  rw [allListChar_eq_one_iff]
  simp [isBinDigit_eq_one_iff]

theorem allBinDigitsChar_le_one (c : ℕ) : allBinDigitsChar c ≤ 1 := by
  unfold allBinDigitsChar; exact allListChar_le_one _ _ _

set_option maxHeartbeats 800000 in
theorem primrec_allBinDigitsChar : Nat.Primrec allBinDigitsChar := by
  unfold allBinDigitsChar
  exact (primrec_foldCode (primrec_allListStp (primrec_isBinDigit.comp Nat.Primrec.left))
    (Nat.Primrec.const 0) (Nat.Primrec.const 1) primrec_id).of_eq fun _ => rfl


theorem nthStp_val (i x s r : ℕ) :
    nthStp (Nat.pair x (Nat.pair (Nat.pair s r) i))
      = Nat.pair (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r) := by
  unfold nthStp; simp only [unpair_pair_fst, unpair_pair_snd]


theorem nthCode_foldl (i : ℕ) : ∀ (l : List ℕ) (s r : ℕ),
    (List.foldl (fun acc x => nthStp (Nat.pair x (Nat.pair acc i))) (Nat.pair s r) l).unpair.2
      = if i < s then r else l.getD (i - s) r := by
  intro l
  induction l with
  | nil => intro s r; simp only [List.foldl_nil, unpair_pair_snd, List.getD_nil]; split <;> rfl
  | cons x l ih =>
    intro s r
    rw [List.foldl_cons, nthStp_val, ih (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r)]
    by_cases h : i = s
    · subst h
      have he : (1 : ℕ) - ((i - i) + (i - i)) = 1 := by omega
      rw [he, selectFn_one, ite_eq_right (lt_irrefl i), ite_eq_left (Nat.lt_succ_self i), Nat.sub_self,
        List.getD_cons_zero]
    · by_cases h2 : i < s
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, ite_eq_left h2, ite_eq_left (Nat.lt_succ_of_lt h2)]
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, ite_eq_right h2, ite_eq_right (show ¬ i < s + 1 by omega),
          show i - s = (i - (s + 1)) + 1 by omega, List.getD_cons_succ]

theorem nthCode_eq (c i d : ℕ) : nthCode c i d = (decodeList c).getD i d := by
  unfold nthCode
  rw [foldCode_eq']
  have h := nthCode_foldl i (decodeList c) 0 d
  rw [ite_eq_right (Nat.not_lt_zero i), Nat.sub_zero] at h
  exact h

theorem primrec_nthStp : Nat.Primrec nthStp := by
  have hcount : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hres : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hbit : Nat.Primrec (fun w : ℕ => 1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
      + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1))) :=
    primrec_sub₂ (Nat.Primrec.const 1)
      (primrec_add₂ (primrec_sub₂ hcount hi) (primrec_sub₂ hi hcount))
  exact ((Nat.Primrec.succ.comp hcount).pair (primrec_selectFn hbit hx hres)).of_eq fun _ => rfl

/-- `nthCode` is primitive recursive in `(c, i, d)` (coded as `pair c (pair i d)`). -/
theorem primrec_nthCode : Nat.Primrec
    (fun t => nthCode t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hfold := primrec_foldCode primrec_nthStp (Nat.Primrec.left.comp Nat.Primrec.right)
    ((Nat.Primrec.const 0).pair (Nat.Primrec.right.comp Nat.Primrec.right)) Nat.Primrec.left
  exact (Nat.Primrec.right.comp hfold).of_eq fun _ => rfl


theorem tabStep_val (g : ℕ → ℕ) (a y IH : ℕ) :
    tabStep g (Nat.pair a (Nat.pair y IH))
      = Nat.pair (g (Nat.pair (a.unpair.1 - 1 - y) a.unpair.2)) IH + 1 := by
  unfold tabStep; simp only [unpair_pair_fst, unpair_pair_snd]


/-- After `K ≤ B` steps the accumulated code decodes to the indices `B-K, …, B-1`. -/
theorem decodeList_tabCode_aux (g : ℕ → ℕ) (B p : ℕ) :
    ∀ K, K ≤ B → decodeList (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)
      = (List.range' (B - K) K).map (fun j => g (Nat.pair j p)) := by
  intro K
  induction K with
  | zero => intro _; simp [decodeList_zero]
  | succ K ih =>
    intro hK
    have hKB : K ≤ B := Nat.le_of_succ_le hK
    show decodeList (tabStep g (Nat.pair (Nat.pair B p) (Nat.pair K
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)))) = _
    rw [tabStep_val]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, ih hKB,
      show B - (K + 1) = B - 1 - K by omega, List.range'_succ, List.map_cons,
      show B - 1 - K + 1 = B - K by omega]

theorem decodeList_tabCode (g : ℕ → ℕ) (B p : ℕ) :
    decodeList (tabCode g (Nat.pair B p) B) = (List.range B).map (fun j => g (Nat.pair j p)) := by
  have h := decodeList_tabCode_aux g B p B (le_refl B)
  rw [Nat.sub_self, ← List.range_eq_range'] at h
  exact h

/-- Choice-free `getD`-as-`getElem` in range. -/
theorem getD_eq_getElem_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ} (h : n < l.length), l.getD n d = l[n] := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.getD_cons_zero, List.getElem_cons_zero]
    | succ m => rw [List.getD_cons_succ, List.getElem_cons_succ]; exact ih _

/-- Choice-free default-out-of-range. -/
theorem getD_eq_default_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → l.getD n d = d := by
  induction l with
  | nil => intro n _; exact List.getD_nil
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m => rw [List.getD_cons_succ]; exact ih (by rw [List.length_cons] at h; omega)

/-- Choice-free `getD` of a mapped `range`. -/
theorem getD_map_range_cf {β : Type*} (h : ℕ → β) (d : β) {B i : ℕ} (hi : i < B) :
    ((List.range B).map h).getD i d = h i := by
  have hlen : ((List.range B).map h).length = B := by rw [List.length_map, List.length_range]
  rw [getD_eq_getElem_cf _ d (by rw [hlen]; exact hi), List.getElem_map, List.getElem_range]

theorem tabCode_nth_lt {g : ℕ → ℕ} {B p i : ℕ} (hi : i < B) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = g (Nat.pair i p) := by
  rw [nthCode_eq, decodeList_tabCode, getD_map_range_cf]; exact hi

theorem tabCode_nth_ge {g : ℕ → ℕ} {B p i : ℕ} (hi : B ≤ i) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = d := by
  rw [nthCode_eq, decodeList_tabCode, getD_eq_default_cf]
  rw [List.length_map, List.length_range]; exact hi

theorem primrec_tabStep {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (tabStep g) := by
  have hB : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hidx : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (primrec_sub₂ hB (Nat.Primrec.const 1)) hk
  exact (Nat.Primrec.succ.comp ((hg.comp (hidx.pair hp)).pair hih)).of_eq fun _ => rfl

/-- `tabCode g · ·` is primitive recursive in `(a, B)` (coded `pair a B`), whenever `g` is. -/
theorem primrec_tabCode {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => tabCode g t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const 0) (primrec_tabStep hg)).of_eq fun t => by
    simp only [Nat.unpaired]; rfl


/-- Tag-dispatch on `e.unpair.1 ∈ {0,1,2,3}` (else `fdef e`). -/
theorem primrec_tagCase4 {f0 f1 f2 f3 fdef : ℕ → ℕ}
    (hf0 : Nat.Primrec f0) (hf1 : Nat.Primrec f1) (hf2 : Nat.Primrec f2) (hf3 : Nat.Primrec f3)
    (hfdef : Nat.Primrec fdef) :
    Nat.Primrec (fun e =>
      let t := e.unpair.1
      selectFn (isOne (1 - t)) (f0 e)
        (selectFn (isOne (2 - t)) (f1 e)
          (selectFn (isOne (3 - t)) (f2 e)
            (selectFn (isOne (4 - t)) (f3 e) (fdef e))))) := by
  have ht : Nat.Primrec (fun e => e.unpair.1) := Nat.Primrec.left
  have h01 : Nat.Primrec (fun e => isOne (1 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) ht)
  have h12 : Nat.Primrec (fun e => isOne (2 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) ht)
  have h23 : Nat.Primrec (fun e => isOne (3 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) ht)
  have h34 : Nat.Primrec (fun e => isOne (4 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) ht)
  refine (primrec_selectFn h01 hf0
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hf2
        (primrec_selectFn h34 hf3 hfdef)))).of_eq fun e => rfl


theorem mulBit_eq_one_iff (a b : ℕ) : mulBit a b = 1 ↔ a = 1 ∧ b = 1 := by
  simp [mulBit]

theorem mulBit_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : mulBit a b ≤ 1 := by
  unfold mulBit
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp

theorem primrec_mulBit : Nat.Primrec (fun t => mulBit t.unpair.1 t.unpair.2) :=
  primrec_mul₂ Nat.Primrec.left Nat.Primrec.right


/-- Tag-dispatch form of `decodeFuelOkCharBody` (**7.22i(b)1(c)**). -/
theorem decodeFuelOkCharBody_eq (prev : ℕ → ℕ) (c : ℕ) :
    decodeFuelOkCharBody prev c =
      match c.unpair.1 with
      | 0 => selectFn (isOne (1 - c.unpair.2)) 1 0
      | 1 => allBinDigitsChar c.unpair.2
      | 2 | 3 => mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)
      | _ => 0 := by
  unfold decodeFuelOkCharBody mulBit
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


theorem primrec_decodeFuelOkCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun c => decodeFuelOkCharBody prev c) := by
  unfold decodeFuelOkCharBody
  have hleft : Nat.Primrec (fun c => prev c.unpair.2.unpair.1) :=
    (hprev.comp (Nat.Primrec.left.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hright : Nat.Primrec (fun c => prev c.unpair.2.unpair.2) :=
    (hprev.comp (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq fun c => by
      simp only
  have hsub : Nat.Primrec (fun c => mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)) :=
    primrec_mul₂ hleft hright
  have hf0 : Nat.Primrec (fun c => selectFn (isOne (1 - c.unpair.2)) 1 0) :=
    primrec_selectFn
      (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) Nat.Primrec.right))
      (Nat.Primrec.const 1) (Nat.Primrec.const 0)
  have hf1 : Nat.Primrec (fun c => allBinDigitsChar c.unpair.2) :=
    primrec_allBinDigitsChar.comp Nat.Primrec.right
  exact primrec_tagCase4 hf0 hf1 hsub hsub (Nat.Primrec.const 0)

theorem decodeFuelOkCharBody_local (f g : ℕ → ℕ) (c : ℕ) (h : ∀ c' ≤ c, f c' = g c') :
    decodeFuelOkCharBody f c = decodeFuelOkCharBody g c := by
  rw [decodeFuelOkCharBody_eq, decodeFuelOkCharBody_eq]
  have h1 : c.unpair.2.unpair.1 ≤ c := le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)
  have h2 : c.unpair.2.unpair.2 ≤ c := le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c)
  rw [h _ h1, h _ h2]


theorem listLenStp_eq (acc x p : ℕ) :
    listLenStp (Nat.pair x (Nat.pair acc p)) = acc + 1 := by
  unfold listLenStp; simp only [unpair_pair_fst, unpair_pair_snd]


theorem listLenChar_eq (c : ℕ) : listLenChar c = (decodeList c).length := by
  have hfun : (fun acc x => listLenStp (Nat.pair x (Nat.pair acc 0))) = fun acc _ => acc + 1 := by
    funext acc x; simp [listLenStp_eq]
  have hfold : ∀ (k : ℕ) (l : List ℕ),
      List.foldl (fun acc _ => acc + 1) k l = k + l.length := by
    intro k l
    induction l generalizing k with
    | nil => simp
    | cons _ xs ih => simp [List.foldl_cons, ih, List.length_cons]; omega
  unfold listLenChar
  rw [foldCode_eq', hfun]
  simp [hfold]

theorem primrec_listLenStp : Nat.Primrec listLenStp :=
  primrec_add₂ (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)

theorem primrec_listLenChar : Nat.Primrec listLenChar := by
  unfold listLenChar
  exact (primrec_foldCode primrec_listLenStp (Nat.Primrec.const 0) (Nat.Primrec.const 0)
    primrec_id).of_eq fun _ => rfl


theorem natEqChar_le_one (a b : ℕ) : natEqChar a b ≤ 1 := by unfold natEqChar; omega

theorem natEqChar_eq_zero_or_one (a b : ℕ) : natEqChar a b = 0 ∨ natEqChar a b = 1 := by
  unfold natEqChar; omega

theorem primrec_natEqChar : Nat.Primrec (fun t => natEqChar t.unpair.1 t.unpair.2) :=
  (primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_add₂ (primrec_sub₂ Nat.Primrec.left Nat.Primrec.right)
      (primrec_sub₂ Nat.Primrec.right Nat.Primrec.left))).of_eq fun _ => rfl


theorem listEqStp_acc (flag rem x : ℕ) :
    listEqStp (Nat.pair x (Nat.pair (Nat.pair flag rem) 0)) =
      selectFn (isZero rem) (Nat.pair 0 0)
        (Nat.pair (selectFn flag (natEqChar x ((rem - 1).unpair.1)) 0) ((rem - 1).unpair.2)) := by
  unfold listEqStp listEqStpNonzero
  simp only [unpair_pair_fst, unpair_pair_snd]


theorem decodeList_eq_nil_iff (c : ℕ) : decodeList c = [] ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg encodeList h
    rwa [encodeList, encodeList_decodeList] at this
  · intro hc; simp [hc, decodeList_zero]

private theorem selectFn_eq_one_iff_zero {a b : ℕ} (ha : a = 0 ∨ a = 1) :
    selectFn a b 0 = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with ha | ha <;> simp [selectFn, ha]

private theorem listEqStep_zero (flag x : ℕ) :
    listEqStep (Nat.pair flag 0) x = Nat.pair 0 0 := by
  simp [listEqStep, listEqStp_acc, isZero, min]

private theorem listEqStep_succ (flag x m : ℕ) :
    listEqStep (Nat.pair flag (m + 1)) x =
      Nat.pair (selectFn flag (natEqChar x m.unpair.1) 0) m.unpair.2 := by
  unfold listEqStep listEqStp listEqStpNonzero
  simp only [unpair_pair_fst, unpair_pair_snd]
  have hzero : isZero (m + 1) = 0 := by
    unfold isZero; simp
  rw [hzero, selectFn_zero, Nat.add_sub_cancel]

private theorem listEq_foldl_zero (flag x : ℕ) (xs : List ℕ) :
    (List.foldl listEqStep (Nat.pair flag 0) (x :: xs)).unpair.1 = 0 := by
  rw [List.foldl_cons, listEqStep_zero]
  induction xs with
  | nil => simp [List.foldl_nil]
  | cons y ys ih =>
    rw [List.foldl_cons, listEqStep_zero, ih]

private theorem listEq_foldl_end_iff (l1 : List ℕ) (flag rem : ℕ) (hflag : flag = 0 ∨ flag = 1) :
    (let r := List.foldl listEqStep (Nat.pair flag rem) l1
     r.unpair.1 = 1 ∧ isZero r.unpair.2 = 1) ↔
      flag = 1 ∧ l1 = decodeList rem := by
  induction l1 generalizing flag rem with
  | nil =>
    simp only [List.foldl_nil, unpair_pair_fst, unpair_pair_snd]
    constructor
    · intro ⟨hflag', hrem0⟩
      have hrem0' : rem = 0 := (isZero_eq_one_iff rem).1 hrem0
      exact ⟨hflag', ((decodeList_eq_nil_iff rem).2 hrem0').symm⟩
    · intro ⟨hflag', heq⟩
      exact ⟨hflag', (isZero_eq_one_iff rem).2 ((decodeList_eq_nil_iff rem).1 heq.symm)⟩
  | cons x xs ih =>
    by_cases hrem : rem = 0
    · subst hrem
      simp only [decodeList_zero]
      constructor
      · intro ⟨h1, _⟩
        have h0 : (let r := List.foldl listEqStep (Nat.pair flag 0) (x :: xs); r.unpair.1) = 0 := by
          show (List.foldl listEqStep (Nat.pair flag 0) (x :: xs)).unpair.1 = 0
          exact listEq_foldl_zero flag x xs
        rw [h0] at h1
        exact absurd h1 (by decide)
      · intro h
        cases h.2
    · rcases rem with _ | m
      · omega
      · set acc' := selectFn flag (natEqChar x m.unpair.1) 0 with hacc'
        have hacc01 : acc' = 0 ∨ acc' = 1 := by
          rcases hflag with h | h
          · left; rw [hacc', h, selectFn_zero]
          · have hz := natEqChar_eq_zero_or_one x m.unpair.1
            rw [hacc', h, selectFn_one]
            rcases hz with hz0 | hz1
            · exact Or.inl hz0
            · exact Or.inr hz1
        rw [List.foldl_cons, listEqStep_succ, ih acc' m.unpair.2 hacc01, decodeList_succ]
        constructor
        · intro ⟨hacc'1, hxs⟩
          have hsel : selectFn flag (natEqChar x m.unpair.1) 0 = 1 := hacc'.trans hacc'1
          rcases (selectFn_eq_one_iff_zero hflag).1 hsel with ⟨hflag1, hxeq⟩
          rw [natEqChar_eq_one_iff] at hxeq
          exact ⟨hflag1, by rw [hxeq, hxs]⟩
        · intro ⟨hflag1, heq⟩
          rcases List.cons.inj heq with ⟨hx, hxs⟩
          refine ⟨hacc'.trans ((selectFn_eq_one_iff_zero hflag).2 ⟨hflag1, by
            rw [natEqChar_eq_one_iff, hx]⟩), hxs⟩

theorem listEqChar_eq_one_iff (c1 c2 : ℕ) :
    listEqChar c1 c2 = 1 ↔ decodeList c1 = decodeList c2 := by
  unfold listEqChar
  rw [foldCode_eq', show (fun acc x => listEqStp (Nat.pair x (Nat.pair acc 0))) = listEqStep from rfl,
    mulBit_eq_one_iff]
  exact (listEq_foldl_end_iff (decodeList c1) 1 c2 (Or.inr rfl)).trans (by simp)

private theorem listEq_foldl_flag_le_one : ∀ (l : List ℕ) (z : ℕ), z.unpair.1 ≤ 1 →
    (List.foldl listEqStep z l).unpair.1 ≤ 1 := by
  intro l
  induction l with
  | nil => intro z hz; exact hz
  | cons x xs ih =>
    intro z hz
    simp only [List.foldl_cons]
    apply ih
    show (listEqStp (Nat.pair x (Nat.pair z 0))).unpair.1 ≤ 1
    have hkey := listEqStp_acc z.unpair.1 z.unpair.2 x
    rw [Nat.pair_unpair] at hkey
    rw [hkey]
    rcases (show isZero z.unpair.2 = 0 ∨ isZero z.unpair.2 = 1 from by
      have := isZero_le_one z.unpair.2; omega) with h0 | h1
    · rw [h0, selectFn_zero, unpair_pair_fst]
      rcases (show z.unpair.1 = 0 ∨ z.unpair.1 = 1 from by omega) with hf0 | hf1
      · rw [hf0, selectFn_zero]; exact Nat.zero_le 1
      · rw [hf1, selectFn_one]
        have := natEqChar_le_one x (z.unpair.2 - 1).unpair.1
        omega
    · rw [h1, selectFn_one, unpair_pair_fst]; exact Nat.zero_le 1

theorem listEqChar_le_one (c1 c2 : ℕ) : listEqChar c1 c2 ≤ 1 := by
  unfold listEqChar
  rw [foldCode_eq', show (fun acc x => listEqStp (Nat.pair x (Nat.pair acc 0))) = listEqStep from rfl]
  exact mulBit_le_one
    (listEq_foldl_flag_le_one (decodeList c1) (Nat.pair 1 c2) (by simp))
    (isZero_le_one _)

set_option maxHeartbeats 800000 in
theorem primrec_listEqStpNonzero : Nat.Primrec listEqStpNonzero := by
  have hflag := Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hrem := Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hhead := Nat.Primrec.left
  have hrem1 := primrec_sub₂ hrem (Nat.Primrec.const 1)
  have hcmp := primrec_natEqChar.comp (hhead.pair (Nat.Primrec.left.comp hrem1))
  have htail := Nat.Primrec.right.comp hrem1
  exact (Nat.Primrec.pair (primrec_selectFn hflag hcmp (Nat.Primrec.const 0)) htail).of_eq fun w => by
    simp [listEqStpNonzero, selectFn]

set_option maxHeartbeats 800000 in
theorem primrec_listEqStp : Nat.Primrec listEqStp := by
  have hrem := Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hzero := Nat.Primrec.pair (Nat.Primrec.const 0) (Nat.Primrec.const 0)
  exact (primrec_selectFn (primrec_isZero.comp hrem) hzero primrec_listEqStpNonzero).of_eq fun w => by
    simp [listEqStp, selectFn, isZero, min]

theorem primrec_listEqChar : Nat.Primrec (fun t => listEqChar t.unpair.1 t.unpair.2) := by
  have hfold := primrec_foldCode primrec_listEqStp (Nat.Primrec.const 0)
    (Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.right) Nat.Primrec.left
  have hflag : Nat.Primrec (fun t =>
      (foldCode listEqStp 0 (Nat.pair 1 t.unpair.2) t.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hfold
  have hrem : Nat.Primrec (fun t =>
      (foldCode listEqStp 0 (Nat.pair 1 t.unpair.2) t.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hfold
  exact (primrec_mulBit.comp (hflag.pair (primrec_isZero.comp hrem))).of_eq fun t => by
    simp [listEqChar]


/-- Two lists agree when every `getD` index does. (Choice-free: `by_contra`/`Classical.choice` is
avoided by case-splitting on `Nat.lt_trichotomy` — a decidable fact — instead.) -/
theorem list_eq_of_getD {l1 l2 : List ℕ} (h : ∀ i d, l1.getD i d = l2.getD i d) : l1 = l2 := by
  have hlen : l1.length = l2.length := by
    rcases Nat.lt_trichotomy l1.length l2.length with hlt | heq | hgt
    · have h1 := h l1.length 1
      have h2 := h l1.length 2
      rw [getD_eq_default_cf l1 _ (Nat.le_refl _), getD_eq_getElem_cf l2 _ (by omega)] at h1 h2
      omega
    · exact heq
    · have h1 := h l2.length 1
      have h2 := h l2.length 2
      rw [getD_eq_getElem_cf l1 _ (by omega), getD_eq_default_cf l2 _ (Nat.le_refl _)] at h1 h2
      omega
  apply List.ext_getElem hlen
  intro i hi _
  have hi' : i < l2.length := by rw [← hlen]; exact hi
  rw [← getD_eq_getElem_cf l1 0 hi, ← getD_eq_getElem_cf l2 0 hi', h i 0]

theorem getD_take_cf (l : List ℕ) (n i d : ℕ) (hi : i < (l.take n).length) :
    (l.take n).getD i d = l.getD i d := by
  have hlen : i < l.length := by
    rw [List.length_take] at hi
    exact Nat.lt_of_lt_of_le hi (Nat.min_le_right n l.length)
  rw [getD_eq_getElem_cf (l.take n) d hi, getD_eq_getElem_cf l d hlen, List.getElem_take]

theorem getD_drop_cf (l : List ℕ) (n i d : ℕ) (hi : i < (l.drop n).length) :
    (l.drop n).getD i d = l.getD (i + n) d := by
  induction n generalizing l i d with
  | zero =>
    simp [List.drop_zero] at hi ⊢
  | succ n ih =>
    cases l with
    | nil => simp [List.drop, List.length_nil] at hi
    | cons a tl =>
      cases i with
      | zero =>
        simp [List.drop]
      | succ i =>
        simp only [List.drop]
        exact ih tl (i + 1) d (by simpa [List.length_drop] using hi)

private theorem isZero_succ_sub_len1 (i len1 : ℕ) :
    isZero ((i + 1) - len1) = 1 ↔ i < len1 := by
  unfold isZero
  constructor
  · intro h
    by_contra hge
    have hpos : 0 < (i + 1) - len1 := Nat.sub_pos_of_lt (Nat.lt_succ_of_le (Nat.le_of_not_gt hge))
    have hmin : min ((i + 1) - len1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
    omega
  · intro hlt
    have : (i + 1) - len1 = 0 := Nat.sub_eq_zero_iff_le.mpr (Nat.succ_le_iff.mpr hlt)
    simp [this, min]

private theorem isZero_succ_sub_len1_zero (i len1 : ℕ) (hge : len1 ≤ i) :
    isZero ((i + 1) - len1) = 0 := by
  unfold isZero
  have hpos : 0 < (i + 1) - len1 := Nat.sub_pos_of_lt (Nat.lt_succ_of_le hge)
  have hmin : min ((i + 1) - len1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
  simp [hmin]

theorem appendListTabFn_eq (c1 c2 len1 i : ℕ) :
    appendListTabFn (Nat.pair i (Nat.pair c1 (Nat.pair c2 len1))) =
      if i < len1 then
        (decodeList c1).getD i 0
      else
        (decodeList c2).getD (i - len1) 0 := by
  unfold appendListTabFn
  simp only [unpair_pair_fst, unpair_pair_snd]
  by_cases hlt : i < len1
  · rw [ite_eq_left hlt, (isZero_succ_sub_len1 i len1).2 hlt, selectFn_one, nthCode_eq]
  · rw [ite_eq_right hlt, isZero_succ_sub_len1_zero i len1 (Nat.le_of_not_gt hlt), selectFn_zero,
      nthCode_eq]

theorem takeCode_eq (n c : ℕ) :
    decodeList (takeCode n c) = (decodeList c).take n := by
  unfold takeCode
  rw [decodeList_tabCode, listLenChar_eq c]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < Nat.min n (decodeList c).length
  · have hic : i < (decodeList c).length := Nat.lt_of_lt_of_le hi (Nat.min_le_right n _)
    rw [getD_map_range_cf (fun j => takeListTabFn (Nat.pair j (Nat.pair n c))) d hi,
      show takeListTabFn (Nat.pair i (Nat.pair n c)) = (decodeList c).getD i d by
        have hc : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.2 = c := by simp
        have hi' : (Nat.pair i (Nat.pair n c)).unpair.1 = i := by simp
        rw [takeListTabFn, hc, hi', nthCode_eq,
          show (decodeList c).getD i 0 = (decodeList c).getD i d from by
            rw [getD_eq_getElem_cf _ 0 hic, getD_eq_getElem_cf _ d hic]],
      getD_take_cf (decodeList c) n i d (by rwa [List.length_take])]
  · have hge : Nat.min n (decodeList c).length ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_take]; exact hge)]

theorem dropCode_eq (n c : ℕ) :
    decodeList (dropCode n c) = (decodeList c).drop n := by
  unfold dropCode
  rw [decodeList_tabCode, listLenChar_eq c]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < (decodeList c).length - n
  · have hic : i + n < (decodeList c).length := Nat.add_lt_of_lt_sub hi
    rw [getD_map_range_cf (fun j => dropListTabFn (Nat.pair j (Nat.pair n c))) d hi,
      show dropListTabFn (Nat.pair i (Nat.pair n c)) = (decodeList c).getD (i + n) d by
        have hc : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.2 = c := by simp
        have hn : (Nat.pair i (Nat.pair n c)).unpair.2.unpair.1 = n := by simp
        have hi' : (Nat.pair i (Nat.pair n c)).unpair.1 = i := by simp
        rw [dropListTabFn, hi', hn, hc, nthCode_eq,
          show (decodeList c).getD (i + n) 0 = (decodeList c).getD (i + n) d from by
            rw [getD_eq_getElem_cf _ 0 hic, getD_eq_getElem_cf _ d hic]],
      getD_drop_cf (decodeList c) n i d (by rw [List.length_drop]; exact hi)]
  · have hge : (decodeList c).length - n ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_drop]; exact hge)]

/-- Taking a prefix never increases the Gödel code (`Nat.pair`'s monotonicity in the second
argument, chained through `encodeList`'s recursive `pair`). -/
theorem encodeList_take_le (l : List ℕ) : ∀ n, encodeList (l.take n) ≤ encodeList l := by
  induction l with
  | nil => intro n; simp [encodeList]
  | cons a l ih =>
    intro n
    cases n with
    | zero => simp [encodeList]
    | succ n =>
      show encodeList (a :: l.take n) ≤ encodeList (a :: l)
      simp only [encodeList]
      exact Nat.add_le_add_right (pair_le_pair_right' a (ih n)) 1

/-- Dropping a suffix never increases the Gödel code. -/
theorem encodeList_drop_le (l : List ℕ) : ∀ n, encodeList (l.drop n) ≤ encodeList l := by
  induction l with
  | nil => intro n; simp [encodeList]
  | cons a l ih =>
    intro n
    cases n with
    | zero => simp [encodeList]
    | succ n =>
      show encodeList (l.drop n) ≤ encodeList (a :: l)
      calc encodeList (l.drop n) ≤ encodeList l := ih n
        _ ≤ Nat.pair a (encodeList l) := le_pair_right a (encodeList l)
        _ ≤ Nat.pair a (encodeList l) + 1 := Nat.le_succ _

theorem takeCode_le (n c : ℕ) : takeCode n c ≤ c := by
  have h1 : takeCode n c = encodeList ((decodeList c).take n) := by
    rw [← takeCode_eq, encodeList_decodeList]
  rw [h1]
  exact le_trans (encodeList_take_le _ n) (le_of_eq (encodeList_decodeList c))

theorem dropCode_le (n c : ℕ) : dropCode n c ≤ c := by
  have h1 : dropCode n c = encodeList ((decodeList c).drop n) := by
    rw [← dropCode_eq, encodeList_decodeList]
  rw [h1]
  exact le_trans (encodeList_drop_le _ n) (le_of_eq (encodeList_decodeList c))

theorem primrec_takeListTabFn : Nat.Primrec takeListTabFn :=
  (primrec_nthCode.comp
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.pair (Nat.Primrec.const 0)))).of_eq fun w => by
    simp [takeListTabFn]

theorem primrec_min {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.min (f n) (g n)) :=
  (primrec_selectFn (primrec_le hf hg) hf hg).of_eq fun n => by
    unfold selectFn isZero Nat.min
    by_cases h : f n ≤ g n
    · simp [Nat.sub_eq_zero_iff_le.mpr h, Nat.min_eq_left h]
    · have hlt : g n < f n := Nat.lt_of_not_ge h
      have hpos : 0 < f n - g n := Nat.sub_pos_of_lt hlt
      have hmin : min (f n - g n) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
      simp [hmin, Nat.min_eq_right (Nat.le_of_lt hlt)]

theorem primrec_takeCode : Nat.Primrec (fun t => takeCode t.unpair.1 t.unpair.2) := by
  have hn := Nat.Primrec.left
  have hc := Nat.Primrec.right
  have hlen := primrec_listLenChar.comp hc
  have hB := primrec_min hn hlen
  have hp := hn.pair hc
  have hr := (hB.pair hp).pair hB
  refine ((primrec_tabCode primrec_takeListTabFn).comp hr).of_eq fun t => by
    simp [takeCode]

theorem primrec_dropListTabFn : Nat.Primrec dropListTabFn :=
  (primrec_nthCode.comp
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.left (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by
    simp [dropListTabFn]

theorem primrec_dropCode : Nat.Primrec (fun t => dropCode t.unpair.1 t.unpair.2) := by
  have hn := Nat.Primrec.left
  have hc := Nat.Primrec.right
  have hlen := primrec_listLenChar.comp hc
  have hB := primrec_sub₂ hlen hn
  have hp := hn.pair hc
  have hr := (hB.pair hp).pair hB
  refine ((primrec_tabCode primrec_dropListTabFn).comp hr).of_eq fun t => by
    simp [dropCode]

open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


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


/-- `Nat.pair 0 t < Nat.pair 1 b` whenever `t < b`, via mathlib's `Nat.pair` monotonicity
in each argument (`pair_lt_pair_right` then `pair_lt_pair_left`). -/
private theorem pair_lt_pair_zero_right {t b : ℕ} (ht : t < b) :
    Nat.pair 0 t < Nat.pair 1 b :=
  lt_trans (Nat.pair_lt_pair_right 0 ht) (Nat.pair_lt_pair_left b Nat.zero_lt_one)

theorem codeBound_ge (n c : ℕ) (hlen : (decodeList c).length ≤ n)
    (hbin : ∀ x ∈ decodeList c, x ≤ 1) : c < codeBound n := by
  induction n generalizing c with
  | zero =>
    have hc : c = 0 := by
      cases c with
      | zero => rfl
      | succ c' => simp [decodeList_succ, List.length_cons] at hlen
    simp [hc, codeBound]
  | succ n ih =>
    cases c with
    | zero => simp [codeBound]
    | succ d =>
      simp only [decodeList_succ, List.length_cons] at hlen
      simp only [decodeList_succ] at hbin
      have htlen : (decodeList d.unpair.2).length ≤ n := by omega
      have htbin : ∀ x ∈ decodeList d.unpair.2, x ≤ 1 := fun x hx =>
        hbin x (List.mem_cons.mpr (Or.inr hx))
      have ht := ih d.unpair.2 htlen htbin
      have hh : d.unpair.1 ≤ 1 := hbin d.unpair.1 (List.mem_cons.mpr (Or.inl rfl))
      have hpair : Nat.pair d.unpair.1 d.unpair.2 < Nat.pair 1 (codeBound n) := by
        rcases (show d.unpair.1 = 0 ∨ d.unpair.1 = 1 by omega) with h0 | h1
        · rw [h0]; exact pair_lt_pair_zero_right ht
        · rw [h1]; exact Nat.pair_lt_pair_right 1 ht
      rw [Nat.pair_unpair] at hpair
      simp only [codeBound]
      omega

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

/-- Round-trip through `c9b5_encodeListBool`/`c9b6_decodeListBool` for a code known to consist
only of binary digits (i.e. `allBinDigitsChar c = 1`). -/
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
end

section
/-- **Swap the two arguments** of a recursively decidable binary relation. -/
theorem RecDecidable₂.swap {r : ℕ → ℕ → Prop} (hr : RecDecidable₂ r) :
    RecDecidable₂ (fun a b => r b a) := by
  have hswap : Nat.Primrec (fun t => Nat.pair t.unpair.2 t.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  refine RecDecidable.of_iff (fun t => ?_) (hr.comp hswap)
  simp only [unpair_pair_fst, unpair_pair_snd]
end

section
/-- **Bounded existential quantifier preserves recursive decidability.** Mirrors
`RecDecidable.bForall`, swapping `bForallFn` for `bExistsFn`. -/
theorem RecDecidable.bExists {p : ℕ → Prop} (hp : RecDecidable p) {bound : ℕ → ℕ}
    (hb : Nat.Primrec bound) :
    RecDecidable (fun n => ∃ i, i < bound n ∧ p (Nat.pair i n)) := by
  obtain ⟨f, hf, hfspec⟩ := hp
  refine ⟨fun n => bExistsFn f n (bound n), ?_, ?_⟩
  · have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2 1
        (isOne (f (Nat.pair w.unpair.2.unpair.1 w.unpair.1)))) :=
      primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 1)
        (primrec_isOne.comp (hf.comp
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
    have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
    refine (hprec.comp (primrec_id.pair hb)).of_eq (fun n => ?_)
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    rfl
  · intro n
    show (∃ i, i < bound n ∧ p (Nat.pair i n)) ↔ bExistsFn f n (bound n) = 1
    rw [bExistsFn_eq_one_iff]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, (hfspec _).mp h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, (hfspec _).mpr h⟩⟩
end

section
/-- **Bounded universal quantifier preserves recursive decidability.** If `p` is recursively decidable
and `bound` is primitive recursive, then `fun n => ∀ i < bound n, p (pair i n)` is recursively
decidable (choice-free). -/
theorem RecDecidable.bForall {p : ℕ → Prop} (hp : RecDecidable p) {bound : ℕ → ℕ}
    (hb : Nat.Primrec bound) :
    RecDecidable (fun n => ∀ i, i < bound n → p (Nat.pair i n)) := by
  obtain ⟨f, hf, hfspec⟩ := hp
  refine ⟨fun n => bForallFn f n (bound n), ?_, ?_⟩
  · have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2
        (isOne (f (Nat.pair w.unpair.2.unpair.1 w.unpair.1))) 0) :=
      primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
        (primrec_isOne.comp (hf.comp
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
        (Nat.Primrec.const 0)
    have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
    refine (hprec.comp (primrec_id.pair hb)).of_eq (fun n => ?_)
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    rfl
  · intro n
    show (∀ i, i < bound n → p (Nat.pair i n)) ↔ bForallFn f n (bound n) = 1
    rw [bForallFn_eq_one_iff]
    exact ⟨fun h i hi => (hfspec _).mp (h i hi), fun h i hi => (hfspec _).mpr (h i hi)⟩
end

section
/-- **From a primitive-recursive `{0,1}` characteristic to `RecDecidable`.** This is the standard
bridge when an executable Bool decider has already been realized as a numeric `{0,1}` function; the
logical equivalence is supplied separately (do not reprove the mathematics). -/
theorem RecDecidable.of_zero_one_char {p : ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (_h01 : ∀ n, f n = 0 ∨ f n = 1) (hfe : ∀ n, p n ↔ f n = 1) : RecDecidable p :=
  ⟨f, hf, hfe⟩
end

section
/-- **Paired `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n m`, reindex to `RecDecidable₂`. -/
theorem RecDecidable₂.of_paired_zero_one_char {r : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (h01 : ∀ t, f t = 0 ∨ f t = 1) (hfe : ∀ n m, r n m ↔ f (Nat.pair n m) = 1) :
    RecDecidable₂ r := by
  unfold RecDecidable₂
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair]
end

section
/-- **Triple `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n (Nat.pair m k)`, reindex to `RecDecidable₃`. -/
theorem RecDecidable₃.of_triple_zero_one_char {r : ℕ → ℕ → ℕ → Prop} {f : ℕ → ℕ}
    (hf : Nat.Primrec f) (h01 : ∀ t, f t = 0 ∨ f t = 1)
    (hfe : ∀ n m k, r n m k ↔ f (Nat.pair n (Nat.pair m k)) = 1) :
    RecDecidable₃ r := by
  unfold RecDecidable₃
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair, pair_unpair]
end

section
theorem codeBound_succ (n : ℕ) : codeBound (n + 1) = Nat.pair 1 (codeBound n) + 1 := rfl
end

section
theorem codeBound_zero : codeBound 0 = 1 := rfl
end

section
theorem consistentBChar_eq_one_iff {fuel : ℕ} {a b : SExpr}
    (h : c9b5_sexprDepth (.cap a b) ≤ fuel) :
    consistentBChar fuel (c9b5_sexprGodelEncode a) (c9b5_sexprGodelEncode b) = 1 ↔
      (denote (.cap a b)).Nonempty := by
  simp only [consistentBChar, ← c9b6_sexprGodelEncode_cap]
  exact decideNonemptyBChar_eq_one_iff h
end

section
theorem decideNonemptyBChar_le_one (fuel c_e : ℕ) : decideNonemptyBChar fuel c_e ≤ 1 :=
  bExistsFn_le_one _ _ _
end

section
/-- Fuel is sized for the *outer* `.cap a b` expression (matching the convention of
`decideNonemptyBChar_eq_one_iff` / `matchesBChar_eq_one_iff`), one more than either child alone
needs, since `c9b5_sexprDepth (.cap a b) = 1 + max (c9b5_sexprDepth a) (c9b5_sexprDepth b)`. -/
theorem consistentBChar_le_one (fuel c1 c2 : ℕ) : consistentBChar fuel c1 c2 ≤ 1 :=
  decideNonemptyBChar_le_one _ _
end

section
theorem decodeFuelOkChar_le_one : ∀ fuel c, decodeFuelOkChar fuel c ≤ 1
  | 0, _ => by simp [decodeFuelOkChar]
  | fuel + 1, c => by
    rw [decodeFuelOkChar, decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      simp
      rcases (show isOne (1 - c.unpair.2) = 0 ∨ isOne (1 - c.unpair.2) = 1 by
        have := isOne_le_one (1 - c.unpair.2); omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact Nat.zero_le 1
      · rw [h1, selectFn_one]
    | 1 =>
      simp
      exact allBinDigitsChar_le_one _
    | 2 | 3 =>
      simp
      exact mulBit_le_one (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.1)
        (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.2)
    | _ + 4 =>
      simp
end

section
/-- The decoded list is no longer than its code. -/
theorem decodeList_length_le (c : ℕ) : (decodeList c).length ≤ c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp [decodeList_zero]
    | succ d =>
      rw [decodeList_succ, List.length_cons]
      have hle := unpair_snd_le d
      have := ih d.unpair.2 (Nat.lt_succ_of_le hle)
      omega
end

section
theorem decodeList_mapPairStep (n acc x : ℕ) :
    decodeList (mapPairStep n acc x) = Nat.pair n x :: decodeList acc := by
  unfold mapPairStep; rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]
end

section
/-- The `{0,1}` indicator of `a = 0`, written via truncated subtraction. -/
theorem eqZero_bit (a : ℕ) : 1 - a = if a = 0 then 1 else 0 := by split <;> omega
end

section
/-- Two `{0,1}`-bounded naturals agreeing on "`= 1`" are equal. -/
theorem eq_of_le_one_iff_one {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (h : x = 1 ↔ y = 1) : x = y := by
  by_cases hx1 : x = 1
  · have hy1 := h.mp hx1; omega
  · have hy1 : y ≠ 1 := fun hy1 => hx1 (h.mpr hy1)
    omega
end

section
theorem existsListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    existsListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc 1 (isOne (g (Nat.pair x p))) := by
  unfold existsListStp; simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem existsListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c
      = List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) 0 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => existsListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) := by
    funext acc x; exact existsListStp_eq g acc x p
  unfold existsListChar; rw [foldCode_eq', hfun]
end

section
theorem existsListChar_le_one (g : ℕ → ℕ) (p c : ℕ) : existsListChar g p c ≤ 1 := by
  have h : ∀ (l : List ℕ) (z : ℕ), z ≤ 1 →
      List.foldl (fun acc x => existsListStp g (Nat.pair x (Nat.pair acc p))) z l ≤ 1 := by
    intro l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons x xs ih =>
      intro z hz
      simp only [List.foldl_cons]
      apply ih
      rw [existsListStp_eq]
      rcases (show z = 0 ∨ z = 1 by omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact isOne_le_one _
      · rw [h1, selectFn_one]
  unfold existsListChar
  rw [foldCode_eq']
  exact h (decodeList c) 0 (Nat.zero_le 1)
end

section
/-- Core induction for the OR-fold: starting from `acc ≤ 1`, the fold is `1` iff `acc = 1` or some
list entry passes the decider `g`. -/
theorem existsList_foldl_eq_one_iff (g : ℕ → ℕ) (p : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
      (List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) acc l = 1 ↔
        acc = 1 ∨ ∃ x ∈ l, g (Nat.pair x p) = 1) := by
  intro l
  induction l with
  | nil => intro acc _; simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false,
      or_false]
  | cons x l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    set acc' := selectFn acc 1 (isOne (g (Nat.pair x p))) with hacc'
    have hacc'le : acc' ≤ 1 := by
      rw [hacc']
      rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact isOne_le_one _
      · rw [h, selectFn_one]
    rw [ih acc' hacc'le]
    constructor
    · rintro (hacc'1 | ⟨y, hy, hyg⟩)
      · rw [hacc'] at hacc'1
        rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
        · rw [h, selectFn_zero, isOne_eq_one_iff] at hacc'1
          exact Or.inr ⟨x, List.mem_cons.mpr (Or.inl rfl), hacc'1⟩
        · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons.mpr (Or.inr hy), hyg⟩
    · rintro (hacc1 | ⟨y, hy, hyg⟩)
      · exact Or.inl (by rw [hacc', hacc1, selectFn_one])
      · rcases List.mem_cons.mp hy with rfl | hy'
        · refine Or.inl ?_
          rw [hacc']
          rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
          · rw [h, selectFn_zero, isOne_eq_one_iff]; exact hyg
          · rw [h, selectFn_one]
        · exact Or.inr ⟨y, hy', hyg⟩
end

section
theorem existsListChar_eq_one_iff (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c = 1 ↔ ∃ x ∈ decodeList c, g (Nat.pair x p) = 1 := by
  rw [existsListChar_eq, existsList_foldl_eq_one_iff g p (decodeList c) 0 (Nat.zero_le 1)]
  simp only [Nat.zero_ne_one, false_or]
end

section
theorem fuelTableStep_nth {bodyLookup : ℕ → ℕ} {bound prevTable i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTableStep bodyLookup bound prevTable) i d = bodyLookup (Nat.pair prevTable i) := by
  unfold fuelTableStep
  rw [tabCode_nth_lt (show i < bound + 1 by omega)]
  simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem fuelTable_succ_nth {bodyLookup : ℕ → ℕ} {bound fuel i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTable bodyLookup bound (fuel + 1)) i d =
      bodyLookup (Nat.pair (fuelTable bodyLookup bound fuel) i) :=
  fuelTableStep_nth hi d
end

section
theorem fuelTable_zero_nth {bodyLookup : ℕ → ℕ} {bound i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTable bodyLookup bound 0) i d = 0 := by
  show nthCode (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1)) i d = 0
  rw [tabCode_nth_lt (show i < bound + 1 by omega)]
end

section
/-- **Course-of-values correctness.** If `bodyLookup` faithfully implements `Body` via table
lookup (`hlookup`), and `Body`'s result at `c` only depends on `prev` restricted to `[0, c]`
(`hlocal` — true whenever `Body`'s own recursive calls are all `≤ c`, e.g. via `Nat.unpair`
projections), then `fuelTable` correctly tabulates the `0`/`Body` fuel recursion on `[0, bound]`. -/
theorem fuelTable_eq_of_recursion {F : ℕ → ℕ → ℕ} {Body : (ℕ → ℕ) → ℕ → ℕ} {bodyLookup : ℕ → ℕ}
    (hF0 : ∀ c, F 0 c = 0) (hFsucc : ∀ fuel c, F (fuel + 1) c = Body (F fuel) c)
    (hlookup : ∀ table c, bodyLookup (Nat.pair table c) = Body (fun c' => nthCode table c' 0) c)
    (hlocal : ∀ (f g : ℕ → ℕ) c, (∀ c' ≤ c, f c' = g c') → Body f c = Body g c) :
    ∀ fuel bound c, c ≤ bound → nthCode (fuelTable bodyLookup bound fuel) c 0 = F fuel c := by
  intro fuel
  induction fuel with
  | zero => intro bound c hc; rw [fuelTable_zero_nth hc, hF0]
  | succ fuel ih =>
    intro bound c hc
    rw [fuelTable_succ_nth hc, hlookup, hFsucc]
    exact hlocal _ _ c fun c' hc' => ih bound c' (le_trans hc' hc)
end

section
theorem autStateCardFuelChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable autStateCardFuelCharLookup bound fuel) c 0 = autStateCardFuelChar fuel c :=
  fuelTable_eq_of_recursion (F := autStateCardFuelChar) (Body := autStateCardFuelCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold autStateCardFuelCharLookup; simp)
    autStateCardFuelCharBody_local
end

section
theorem decodeFuelOkChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable decodeFuelOkCharLookup bound fuel) c 0 = decodeFuelOkChar fuel c :=
  fuelTable_eq_of_recursion (F := decodeFuelOkChar) (Body := decodeFuelOkCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold decodeFuelOkCharLookup; simp)
    decodeFuelOkCharBody_local
end

section
/-- The `{0,1}` indicator of `2 ≤ a`, written via truncated subtraction. -/
theorem geTwo_bit (a : ℕ) : 1 - (2 - a) = if 2 ≤ a then 1 else 0 := by split <;> omega
end

section
/-- Choice-free `getD` of a left append. -/
theorem getD_append_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, n < l.length → (l ++ l').getD n d = l.getD n d := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.cons_append, List.getD_cons_zero, List.getD_cons_zero]
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by rw [List.length_cons] at h; omega)
end

section
/-- Choice-free `getD` of a right append. -/
theorem getD_append_right_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → (l ++ l').getD n d = l'.getD (n - l.length) d := by
  induction l with
  | nil => intro n _; rw [List.nil_append, List.length_nil, Nat.sub_zero]
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ]
      exact ih (by rw [List.length_cons] at h; omega)
end

section
theorem appendListCode_eq (c1 c2 : ℕ) :
    decodeList (appendListCode c1 c2) = decodeList c1 ++ decodeList c2 := by
  unfold appendListCode
  rw [decodeList_tabCode, listLenChar_eq c1, listLenChar_eq c2]
  apply list_eq_of_getD
  intro i d
  by_cases hi : i < (decodeList c1).length + (decodeList c2).length
  · have hf := appendListTabFn_eq c1 c2 (decodeList c1).length i
    rw [getD_map_range_cf
        (fun j => appendListTabFn (Nat.pair j (Nat.pair c1 (Nat.pair c2 (decodeList c1).length)))) d hi,
      hf]
    by_cases hlt : i < (decodeList c1).length
    · rw [ite_eq_left hlt,
        show (decodeList c1).getD i 0 = (decodeList c1).getD i d from by
          rw [getD_eq_getElem_cf _ 0 hlt, getD_eq_getElem_cf _ d hlt],
        (getD_append_cf (decodeList c1) (decodeList c2) d hlt).symm]
    · rw [ite_eq_right hlt,
        show (decodeList c2).getD (i - (decodeList c1).length) 0 =
            (decodeList c2).getD (i - (decodeList c1).length) d from by
          have hi2 : i - (decodeList c1).length < (decodeList c2).length := by
            have hle : (decodeList c1).length ≤ i := Nat.le_of_not_gt hlt
            omega
          rw [getD_eq_getElem_cf _ 0 hi2, getD_eq_getElem_cf _ d hi2],
        (getD_append_right_cf (decodeList c1) (decodeList c2) d (Nat.le_of_not_gt hlt)).symm]
  · have hge : (decodeList c1).length + (decodeList c2).length ≤ i := Nat.le_of_not_gt hi
    rw [getD_eq_default_cf _ d (by rw [List.length_map, List.length_range]; exact hge),
      getD_eq_default_cf _ d (by rw [List.length_append]; exact hge)]
end

section
theorem halfParity_spec (n : ℕ) : halfParity n = Nat.pair (n / 2) (n % 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.pair ((halfParity n).unpair.1 + (halfParity n).unpair.2) (1 - (halfParity n).unpair.2)
        = Nat.pair ((n + 1) / 2) ((n + 1) % 2)
    rw [ih, unpair_pair_fst, unpair_pair_snd]
    congr 1 <;> omega
end

section
theorem interEqChar_eq_one_iff {fuel : ℕ} {e1 e2 : SExpr}
    (h1 : c9b5_sexprDepth e1 ≤ fuel) (h2 : c9b5_sexprDepth e2 ≤ fuel) :
    interEqChar fuel (c9b5_sexprGodelEncode e1) (c9b5_sexprGodelEncode e2) = 1 ↔
      denote e1 = denote e2 := by
  unfold interEqChar
  rw [mulBit_eq_one_iff, subsetBChar_eq_one_iff h1 h2, subsetBChar_eq_one_iff h2 h1,
    ← Set.Subset.antisymm_iff]
end

section
theorem mapPairStp_eq (n acc x : ℕ) :
    mapPairStp (Nat.pair x (Nat.pair acc n)) = mapPairStep n acc x := by
  unfold mapPairStp; simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem decodeList_foldl_mapPairStp (n : ℕ) (el : List ℕ) (acc : ℕ) :
    decodeList (List.foldl (fun acc x => mapPairStp (Nat.pair x (Nat.pair acc n))) acc el)
      = (el.map (Nat.pair n ·)).reverse ++ decodeList acc := by
  induction el generalizing acc with
  | nil => simp
  | cons e el ih =>
    rw [List.foldl_cons, ih, mapPairStp_eq, decodeList_mapPairStep, List.map_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]
end

section
theorem decodeList_mapPairCode (n c : ℕ) :
    decodeList (mapPairCode n c) = ((decodeList c).map (Nat.pair n ·)).reverse := by
  unfold mapPairCode
  rw [foldCode_eq']
  have h := decodeList_foldl_mapPairStp n (decodeList c) 0
  rwa [decodeList_zero, List.append_nil] at h
end

section
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
end

section
theorem primrec_allListChar {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => allListChar g t.unpair.2 t.unpair.1) :=
  (primrec_foldCode (primrec_allListStp hg) Nat.Primrec.right (Nat.Primrec.const 1)
    Nat.Primrec.left).of_eq fun _ => rfl
end

section
/-- **Bounded `∀` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∀ e ∈ decodeList c, q e p` is too (the list is coded by
the first argument, `p` is a free parameter). Choice-free. -/
theorem RecDecidable₂.bForallList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∀ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => allListChar g t.unpair.2 t.unpair.1, primrec_allListChar hgp, fun t => ?_⟩
  show (∀ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ allListChar g t.unpair.2 t.unpair.1 = 1
  rw [allListChar_eq_one_iff]
  refine forall_congr' fun e => forall_congr' fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this
end

section
theorem primrec_appendListTabFn : Nat.Primrec appendListTabFn := by
  have hi := Nat.Primrec.left
  have hp := Nat.Primrec.right
  have hlen1 := Nat.Primrec.right.comp (Nat.Primrec.right.comp hp)
  have hc1 := Nat.Primrec.left.comp hp
  have hc2 := Nat.Primrec.left.comp (Nat.Primrec.right.comp hp)
  have hlt := primrec_isZero.comp
    (primrec_sub₂ (primrec_add₂ hi (Nat.Primrec.const 1)) hlen1)
  have hleft := primrec_nthCode.comp (hc1.pair (Nat.Primrec.pair hi (Nat.Primrec.const 0)))
  have hright := primrec_nthCode.comp
    (hc2.pair (Nat.Primrec.pair (primrec_sub₂ hi hlen1) (Nat.Primrec.const 0)))
  exact (primrec_selectFn hlt hleft hright).of_eq fun w => by
    unfold appendListTabFn
    simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem primrec_appendListCode : Nat.Primrec (fun t => appendListCode t.unpair.1 t.unpair.2) := by
  have hc1 := Nat.Primrec.left
  have hc2 := Nat.Primrec.right
  have hlen1 := primrec_listLenChar.comp hc1
  have hlen2 := primrec_listLenChar.comp hc2
  have hsum := primrec_add₂ hlen1 hlen2
  have hp := hc1.pair (hc2.pair hlen1)
  have hr := (hsum.pair hp).pair hsum
  refine ((primrec_tabCode primrec_appendListTabFn).comp hr).of_eq fun t => by
    unfold appendListCode
    simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem primrec_autStateCardFuelChar : ∀ fuel, Nat.Primrec (fun c => autStateCardFuelChar fuel c)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [autStateCardFuelChar] using
      primrec_autStateCardFuelCharBody (primrec_autStateCardFuelChar fuel)
end

section
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
end

section
/-- Parametrized variant of `bForallFn`'s joint primrec (mirrors `primrec_bExistsFn_param`,
swapping `selectFn`'s branches to match `bForallFn`'s `1`-base / AND-style step). -/
theorem primrec_bForallFn_param {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bForallFn (fun p => g (Nat.pair t.unpair.1.unpair.1 p))
      t.unpair.1.unpair.2 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2
        (isOne (g (Nat.pair w.unpair.1.unpair.1
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)))) 0) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (primrec_isOne.comp (hg.comp
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
          (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
            (Nat.Primrec.right.comp Nat.Primrec.left)))))
      (Nat.Primrec.const 0)
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl
end

section
theorem primrec_codeBound : Nat.Primrec codeBound := by
  have hstep : Nat.Primrec (fun w => Nat.pair 1 w.unpair.2 + 1) :=
    primrec_add₂ (Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.right)
      (Nat.Primrec.const 1)
  have haux : ∀ n, Nat.rec (motive := fun _ => ℕ) 1
      (fun y IH => Nat.pair 1 (Nat.pair y IH).unpair.2 + 1) n = codeBound n := by
    intro n
    induction n with
    | zero => simp [codeBound]
    | succ n ih =>
      simp only [unpair_pair_snd] at ih ⊢
      simp [codeBound, ih]
  exact (Nat.Primrec.prec1 1 hstep).of_eq haux
end

section
theorem primrec_decodeFuelOkChar : ∀ fuel, Nat.Primrec (fun c => decodeFuelOkChar fuel c)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [decodeFuelOkChar] using
      primrec_decodeFuelOkCharBody (primrec_decodeFuelOkChar fuel)
end

section
theorem primrec_decodeFuelOkCharLookup : Nat.Primrec decodeFuelOkCharLookup := by
  have hleft : Nat.Primrec (fun w => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by simp
  have hright : Nat.Primrec (fun w => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right))
        (Nat.Primrec.const 0)))).of_eq fun w => by simp
  have hsub : Nat.Primrec (fun w =>
      mulBit (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0)
        (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0)) :=
    primrec_mul₂ hleft hright
  have hf0 : Nat.Primrec (fun w => selectFn (isOne (1 - w.unpair.2.unpair.2)) 1 0) :=
    primrec_selectFn
      (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) (Nat.Primrec.right.comp Nat.Primrec.right)))
      (Nat.Primrec.const 1) (Nat.Primrec.const 0)
  have hf1 : Nat.Primrec (fun w => allBinDigitsChar w.unpair.2.unpair.2) :=
    primrec_allBinDigitsChar.comp (Nat.Primrec.right.comp Nat.Primrec.right)
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
      (primrec_selectFn h23 hsub
        (primrec_selectFn h34 hsub (Nat.Primrec.const 0))))).of_eq fun w => ?_
  show _ = decodeFuelOkCharBody (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2
  rw [decodeFuelOkCharBody_eq]
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
end

section
theorem primrec_existsListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (existsListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc (Nat.Primrec.const 1) hcall).of_eq fun _ => rfl
end

section
theorem primrec_existsListChar {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => existsListChar g t.unpair.2 t.unpair.1) :=
  (primrec_foldCode (primrec_existsListStp hg) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl
end

section
/-- **Bounded `∃` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∃ e ∈ decodeList c, q e p` is too. Choice-free. -/
theorem RecDecidable₂.bExistsList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∃ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => existsListChar g t.unpair.2 t.unpair.1, primrec_existsListChar hgp, fun t => ?_⟩
  show (∃ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ existsListChar g t.unpair.2 t.unpair.1 = 1
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this
end

section
set_option maxHeartbeats 1000000 in
/-- `fuelTable bodyLookup · ·` is primitive recursive in `(bound, fuel)` (coded `pair bound
fuel`), whenever `bodyLookup` is. Mirrors `primrec_tabCode`'s `Nat.Primrec.prec` packaging. -/
theorem primrec_fuelTable {bodyLookup : ℕ → ℕ} (hbodyLookup : Nat.Primrec bodyLookup) :
    Nat.Primrec (fun t => fuelTable bodyLookup t.unpair.1 t.unpair.2) := by
  have hgLookup : Nat.Primrec (fun v => bodyLookup (Nat.pair v.unpair.2 v.unpair.1)) :=
    hbodyLookup.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)
  have htab := primrec_tabCode hgLookup
  have hf : Nat.Primrec (fun bound => tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1)) :=
    ((primrec_tabCode (Nat.Primrec.const 0)).comp
      (Nat.Primrec.pair
        (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)) (Nat.Primrec.const 0))
        (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)))).of_eq fun bound => by simp
  have hpack : Nat.Primrec (fun w =>
      Nat.pair (Nat.pair (w.unpair.1 + 1) w.unpair.2.unpair.2) (w.unpair.1 + 1)) :=
    Nat.Primrec.pair
      (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
        (Nat.Primrec.right.comp Nat.Primrec.right))
      (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
  have hg : Nat.Primrec (fun w => fuelTableStep bodyLookup w.unpair.1 w.unpair.2.unpair.2) :=
    (htab.comp hpack).of_eq fun w => by simp [fuelTableStep]
  have haux : ∀ bound fuel, Nat.rec (motive := fun _ => ℕ)
      (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1))
      (fun _ IH => fuelTableStep bodyLookup bound IH) fuel = fuelTable bodyLookup bound fuel := by
    intro bound fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih => show fuelTableStep bodyLookup bound _ = fuelTableStep bodyLookup bound _; rw [ih]
  refine (Nat.Primrec.prec hf hg).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact haux t.unpair.1 t.unpair.2
end

section
/-- **`autStateCardFuelChar` is jointly primitive recursive in `(fuel, code)`.** -/
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
end

section
/-- **`decodeFuelOkChar` is jointly primitive recursive in `(fuel, code)`.** -/
theorem primrec_decodeFuelOkChar2 : Nat.Primrec (fun s => decodeFuelOkChar s.unpair.1 s.unpair.2) := by
  have hft := primrec_fuelTable primrec_decodeFuelOkCharLookup
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable decodeFuelOkCharLookup s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable decodeFuelOkCharLookup s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (Nat.Primrec.pair hcomp (Nat.Primrec.pair Nat.Primrec.right (Nat.Primrec.const 0)))).of_eq
      fun s => by simp
  exact hnth.of_eq fun s => decodeFuelOkChar_fuelTable_eq s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)
end

section
theorem primrec_halfParity : Nat.Primrec halfParity := by
  have hIH : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hstep : Nat.Primrec (fun w => Nat.pair (w.unpair.2.unpair.2.unpair.1 + w.unpair.2.unpair.2.unpair.2)
      (1 - w.unpair.2.unpair.2.unpair.2)) :=
    (primrec_add₂ (Nat.Primrec.left.comp hIH) (Nat.Primrec.right.comp hIH)).pair
      (primrec_sub₂ (Nat.Primrec.const 1) (Nat.Primrec.right.comp hIH))
  refine ((Nat.Primrec.prec (Nat.Primrec.const 0) hstep).comp
    ((Nat.Primrec.const 0).pair primrec_id)).of_eq (fun n => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rfl
end

section
theorem primrec_div2 : Nat.Primrec (fun n => n / 2) :=
  (Nat.Primrec.left.comp primrec_halfParity).of_eq fun n => by
    rw [halfParity_spec, unpair_pair_fst]
end

section
/-- Primitive-recursive `if` on a `{0,1}` condition. -/
theorem primrec_ite {c t f : ℕ → ℕ} (hc : Nat.Primrec c) (ht : Nat.Primrec t) (hf : Nat.Primrec f) :
    Nat.Primrec (fun n => selectFn (c n) (t n) (f n)) :=
  primrec_selectFn hc ht hf
end

section
theorem primrec_mapPairStp : Nat.Primrec mapPairStp := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((h22.pair h1).pair h21)).of_eq (fun _ => rfl)
end

section
theorem primrec_mapPairCode : Nat.Primrec (fun t => mapPairCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_mapPairStp Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq (fun _ => rfl)
end

section
/-- **Parameterised bounded `∀` over a coded list preserves recursive enumerability.** If `p` is an
r.e. binary relation then `fun t => ∀ e ∈ decodeList t.2, p t.1 e` is r.e.: re-code the list into the
pairs `⟨t.1, e⟩` (`mapPairCode`) and apply the unparameterised `forall_mem_decodeList`. -/
theorem REPred.forall_mem_decodeList₂ {p : ℕ → ℕ → Prop} (hp : REPred₂ p) :
    REPred (fun t => ∀ e ∈ decodeList t.unpair.2, p t.unpair.1 e) := by
  have hp' : REPred (fun s => p s.unpair.1 s.unpair.2) := hp
  have hbase : REPred (fun c => ∀ e' ∈ decodeList c, p e'.unpair.1 e'.unpair.2) :=
    hp'.forall_mem_decodeList
  refine REPred.of_iff (fun t => ?_) (hbase.comp primrec_mapPairCode)
  rw [decodeList_mapPairCode]
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · rintro hall e' ⟨e, he, rfl⟩
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact hall e he
  · intro hall e he
    simpa only [unpair_pair_fst, unpair_pair_snd]
      using hall (Nat.pair t.unpair.1 e) ⟨e, he, rfl⟩
end

section
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
end

section
theorem primrec_matchesBChar : ∀ fuel, Nat.Primrec (fun t => matchesBChar fuel t.unpair.1 t.unpair.2)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [matchesBChar] using
      primrec_matchesBCharBody (primrec_matchesBChar fuel)
end

section
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
end

section
theorem primrec_consistentBChar (fuel : ℕ) :
    Nat.Primrec (fun t => consistentBChar fuel t.unpair.1 t.unpair.2) :=
  (primrec_decideNonemptyBChar fuel).comp
    (Nat.Primrec.pair (Nat.Primrec.const 3)
      (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right))
end

section
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
end

section
/-- **`matchesBChar` is jointly primitive recursive in `(fuel, sexprCode, wordCode)`.** -/
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
end

section
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
end

section
/-- **`consistentBChar` is jointly primitive recursive in `(fuel, c1, c2)`.** -/
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
end

section
/-- `{0,1}`-valued `max` of two primitive-recursive functions. -/
theorem primrec_max {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.max (f n) (g n)) := by
  refine (primrec_selectFn (primrec_le hf hg) hg hf).of_eq fun n => by
    unfold selectFn isZero Nat.max
    by_cases h : f n ≤ g n
    · simp [Nat.sub_eq_zero_iff_le.mpr h, Nat.max_eq_right h]
    · have hlt : g n < f n := Nat.lt_of_not_ge h
      have hpos : 0 < f n - g n := Nat.sub_pos_of_lt hlt
      have hmin : min (f n - g n) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
      simp [hmin, Nat.max_eq_left (Nat.le_of_lt hlt)]
end

section
/-- `Nat.max n 1` is primitive recursive. -/
theorem primrec_max_one : Nat.Primrec (fun n => Nat.max n 1) := by
  refine (primrec_selectFn (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))
    (Nat.Primrec.const 1) primrec_id).of_eq fun n => by
    unfold selectFn isOne Nat.max
    rcases n with _ | n <;> simp
end

section
theorem primrec_mod2 : Nat.Primrec (fun n => n % 2) :=
  (Nat.Primrec.right.comp primrec_halfParity).of_eq fun n => by
    rw [halfParity_spec, unpair_pair_snd]
end

section
theorem primrec_lowOr : Nat.Primrec (fun t => lowOr t.unpair.1 t.unpair.2) := by
  have hx : Nat.Primrec (fun t : ℕ => t.unpair.1 % 2) := primrec_mod2.comp Nat.Primrec.left
  have hy : Nat.Primrec (fun t : ℕ => t.unpair.2 % 2) := primrec_mod2.comp Nat.Primrec.right
  exact (primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_sub₂ (Nat.Primrec.const 1) (primrec_add₂ hx hy))).of_eq fun _ => rfl
end

section
theorem primrec_lorStep : Nat.Primrec lorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowOr s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowOr.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl
end

section
/-- **Bitwise OR is primitive recursive** (the `Nat.unpaired` form), choice-free. -/
theorem primrec_myLor : Nat.Primrec (fun t => myLor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => lorStep w.unpair.2.unpair.2) :=
    primrec_lorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl
end

section
/-- An always-true predicate is recursively decidable (constant decider `1`). -/
theorem recDecidable_of_forall {p : ℕ → Prop} (h : ∀ n, p n) : RecDecidable p :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun n => ⟨fun _ => rfl, fun _ => h n⟩⟩
end

section
/-- An always-true predicate is recursively enumerable. -/
theorem rePred_of_forall {p : ℕ → Prop} (h : ∀ n, p n) : REPred p :=
  (recDecidable_of_forall h).re
end

section
/-- An always-true binary relation is recursively decidable (constant decider `1`). -/
theorem recDecidable₂_of_forall {r : ℕ → ℕ → Prop} (h : ∀ n m, r n m) : RecDecidable₂ r :=
  recDecidable_of_forall (fun t => h t.unpair.1 t.unpair.2)
end

section
/-- `Nat.rec 1 (· * b)` computes `b ^ e` (choice-free). -/
theorem recPow_eq (b : ℕ) :
    ∀ e, Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => ih * b) e = b ^ e
  | 0 => (pow_zero b).symm
  | e + 1 => by rw [pow_succ]; exact congrArg (· * b) (recPow_eq b e)
end

section
/-- **Exponentiation is primitive recursive** (`unpaired (b, e) ↦ b ^ e`), choice-free. -/
theorem primrec_pow : Nat.Primrec (Nat.unpaired fun b e => b ^ e) := by
  have hg : Nat.Primrec (fun w => w.unpair.2.unpair.2 * w.unpair.1) :=
    primrec_mul₂ (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  refine (Nat.Primrec.prec (Nat.Primrec.const 1) hg).of_eq (fun p => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact recPow_eq p.unpair.1 p.unpair.2
end

section
/-- `fun n => f n ^ g n` is primitive recursive. -/
theorem primrec_pow₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n ^ g n) :=
  (primrec_pow.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
end

section
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
end

section
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
end

section
/-- `n ↦ 2 ^ g n` is primitive recursive when `g` is. -/
theorem primrec_two_pow {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (fun n => 2 ^ g n) :=
  (primrec_pow.comp ((Nat.Primrec.const 2).pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
end

section
theorem selectFn_isOne_one_sub_sigma (u : ℕ) :
    selectFn (isOne (1 - u)) 1 0 = 1 ↔ u = 0 := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact hu
    · have : isOne (1 - u) = 0 := isOne_of_ne_one (by omega)
      simp [this, selectFn_zero] at h
  · intro hu
    subst hu
    simp [isOne_one, selectFn_one]
end

section
theorem subsetBChar_le_one (fuel c1 c2 : ℕ) : subsetBChar fuel c1 c2 ≤ 1 := by
  unfold subsetBChar; exact bForallFn_le_one _ _ _
end

section
theorem interEqChar_le_one (fuel c1 c2 : ℕ) : interEqChar fuel c1 c2 ≤ 1 := by
  unfold interEqChar; exact mulBit_le_one (subsetBChar_le_one _ _ _) (subsetBChar_le_one _ _ _)
end

end Domain.Recursive
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

section
variable {α : Type*}

/-- **Definition 7.1 (Scott 1981, PRG-19).** A *computable presentation* of a neighbourhood system
`V` over a token type `α`: an enumeration `X : ℕ → Set α` whose range is exactly `𝒟` (`mem_X` and
`surj`), such that Scott's two relations on the integer indices are recursively decidable:

* `interEq_computable` is (i): the ternary relation `Xₙ ∩ Xₘ = X_k`;
* `cons_computable` is (ii): the binary consistency relation `∃ k. X_k ⊆ Xₙ ∩ Xₘ`
  (Scott's `X_k ⊆ Xₙ and X_k ⊆ Xₘ`).

Only the enumeration `X` is data; the remaining fields are `Prop`s, so a presentation is built
choice-free. -/
structure ComputablePresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`: every neighbourhood appears as some `Xₙ`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(i)** — `Xₙ ∩ Xₘ = X_k` is recursively decidable in `n, m, k`. -/
  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)
  /-- A **primitive-recursive intersection function**: an index of `Xₙ ∩ Xₘ` whenever that
  intersection is a neighbourhood (i.e. consistent). This makes explicit the operation that 7.1(i)
  is *about*: in Scott's general-recursive reading of "recursively decidable" the index can be
  recovered from `interEq_computable` by an (unbounded) search `μk. Xₙ ∩ Xₘ = X_k`, but that search
  is not *primitive* recursive; for the function-space presentation (Theorem 7.5) we need to
  *form* component intersections primitively, so we carry the function as part of the data of an
  ("acceptable") computable presentation. Off the consistent domain `inter n m` may be junk. -/
  inter : ℕ → ℕ → ℕ
  /-- The intersection function is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  inter_primrec : Nat.Primrec (fun t => inter t.unpair.1 t.unpair.2)
  /-- `inter n m` indexes `Xₙ ∩ Xₘ` whenever that intersection is consistent. -/
  inter_spec : ∀ {n m : ℕ}, (∃ k, X k ⊆ X n ∩ X m) → X (inter n m) = X n ∩ X m
  /-- A fixed index of the master neighbourhood `Δ` (used to seed finite intersections). -/
  masterIdx : ℕ
  /-- `X masterIdx = Δ`. -/
  masterIdx_spec : X masterIdx = V.master

/-- **Definition 7.1 (Scott 1981, PRG-19) — effectively given.** A neighbourhood system is
*effectively given* when it admits a computable presentation. -/
def NeighborhoodSystem.IsEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ComputablePresentation V)

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- Reindexing `(n, m) ↦ (n, m, n)` on `Nat.pair` codes: `t ↦ pair n (pair m n)`. -/
def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

/-- **Reindexing a computable presentation along a primitive-recursive involution.** Given
`φ : ℕ → ℕ` with `φ ∘ φ = id` (so `φ` is automatically a bijection, with itself as inverse) and
`Nat.Primrec φ`, transport `P`'s enumeration and both deciders along `φ`: `X' n := P.X (φ n)`.
Every one of Scott's structural fields transfers by straightforward reindexing (`RecDecidable.comp`
against the pairwise-`φ`-reindexing code), so this is a genuinely choice-free construction — used
to re-point a presentation's `0`-th index at an arbitrary target (Theorem 8.8(b)'s `D₀ ≅ D` shift,
via `eIdx`). -/
def reindexInvolutive (P : ComputablePresentation V) (φ : ℕ → ℕ)
    (hφinv : Function.Involutive φ) (hφp : Nat.Primrec φ) : ComputablePresentation V where
  X n := P.X (φ n)
  mem_X n := P.mem_X (φ n)
  surj := fun {Y} hY => by
    obtain ⟨k, hk⟩ := P.surj hY
    exact ⟨φ k, by rw [hφinv k]; exact hk⟩
  interEq_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (Nat.pair (φ t.unpair.2.unpair.1) (φ t.unpair.2.unpair.2))) :=
      (hφp.comp Nat.Primrec.left).pair
        ((hφp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (hφp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
  cons_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨φ k, hk⟩
    · rintro ⟨k, hk⟩; exact ⟨φ k, by rwa [hφinv]⟩
  inter n m := φ (P.inter (φ n) (φ m))
  inter_primrec := by
    have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    exact (hφp.comp ((P.inter_primrec.comp hreindex))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  inter_spec {n m} h := by
    show P.X (φ (φ (P.inter (φ n) (φ m)))) = P.X (φ n) ∩ P.X (φ m)
    rw [hφinv]
    obtain ⟨k, hk⟩ := h
    exact P.inter_spec ⟨φ k, hk⟩
  masterIdx := φ P.masterIdx
  masterIdx_spec := by show P.X (φ (φ P.masterIdx)) = V.master; rw [hφinv]; exact P.masterIdx_spec

/-- Swap the two components of a `Nat.pair` code: `t ↦ pair m n`. -/
def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

end ComputablePresentation

end

section
variable {α : Type*}

/-- The trivial presentation of the one-point system `𝟙 = unitSys`: the constant enumeration
`Xₙ = Δ = univ`. Both of Scott's relations are *always true* here (any two neighbourhoods are equal
and consistent), hence trivially recursively decidable via the constant `1` decider. -/
def unitPresentation : ComputablePresentation unitSys where
  X _ := Set.univ
  mem_X _ := rfl
  surj := by rintro Y rfl; exact ⟨0, rfl⟩
  interEq_computable := recDecidable_of_forall fun _ => Set.inter_self Set.univ
  cons_computable := recDecidable_of_forall fun _ =>
    ⟨0, by rw [Set.inter_self]⟩
  inter _ _ := 0
  inter_primrec := Nat.Primrec.zero
  inter_spec _ := by rw [Set.inter_self]
  masterIdx := 0
  masterIdx_spec := rfl

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)


theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)


private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

/-- **Scott's biconditional after 7.1.** "The inclusion relation between neighbourhoods is itself
decidable in terms of the indices", because `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. We obtain the decision by
reindexing `(n, m) ↦ (n, m, n)` into relation (i). -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

/-- **Equality of neighbourhoods is decidable** from the indices: `Xₙ = Xₘ ↔ Xₙ ⊆ Xₘ ∧ Xₘ ⊆ Xₙ`,
so equality is the conjunction of `incl_computable` with its swap. -/
theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff


end ComputablePresentation

end

section
variable {α : Type*}

/-- **The one-point domain `𝟙` is effectively given.** -/
theorem unitSys_isEffectivelyGiven : unitSys.IsEffectivelyGiven :=
  ⟨unitPresentation⟩
end

namespace Exercise722
open Set Domain.Recursive

section
/-- Definition 7.1 restricted to relation (ii) only (no `interEq_computable`, unlike
`ComputablePresentation`/`ScottPresentation` in `Definition71.lean`/`Exercise715.lean`, whose
pattern this mirrors). -/
structure ConsistencyPresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)
end

end Exercise722
open NeighborhoodSystem Domain.Recursive ApproximableMap

end DomainTheory.NeighbourhoodSystems
end
