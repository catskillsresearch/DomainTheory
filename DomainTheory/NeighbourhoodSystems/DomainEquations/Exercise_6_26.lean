module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_24

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_21
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510
section
namespace Exercise619
variable {D : NeighborhoodSystem Str}
/- concordance: source L4187 EXERCISE 6.26 lifting a domain -/
/-- **Exercise 6.26 — the lifted system `𝒟_⊥` over `{0,1}*`.** A neighbourhood is the master
`{Λ} ∪ 0Δ` or a tagged copy `0X` (`X ∈ 𝒟`). `∅`-freeness of `𝒟` (`hD`) keeps it `∅`-free. -/
def liftTok (D : NeighborhoodSystem Str) (_hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = liftTokMaster D ∨ ∃ X, D.mem X ∧ W = embBit false X
  master := liftTokMaster D
  master_nonempty := ⟨[], nil_mem_liftTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_liftTokMaster hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [liftTokMaster_inter_embF hX']; exact Or.inr ⟨X', hX', rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_comm, liftTokMaster_inter_embF hX]; exact Or.inr ⟨X, hX, rfl⟩
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z', hZ', rfl⟩
        · exact absurd (hZsub nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X ∩ X', D.inter_mem hX hX' hZ' (embBit_subset.mp hZsub), rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **fresh bottom** of `𝒟_⊥`: the element whose only neighbourhood is the master `{Λ} ∪ 0Δ`. -/
def liftBot (D : NeighborhoodSystem Str) (hD : ∀ X, D.mem X → X.Nonempty) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D
  sub := by rintro W rfl; exact Or.inl rfl
  master_mem := rfl
  inter_mem := by rintro W W' rfl rfl; rw [Set.inter_self]
  up_mem := by
    rintro W W' rfl hW' hsub
    exact Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub

theorem liftTok_mem_embF {X : Set Str} (hX : D.mem X) :
    (liftTok D hD).mem (embBit false X) := Or.inr ⟨X, hX, rfl⟩

theorem liftTok_mem_embF_inv {W : Set Str} (h : (liftTok D hD).mem (embBit false W)) : D.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem liftTok_nonempty (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ W, (liftTok D hD).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩)
  · exact ⟨[], nil_mem_liftTokMaster⟩
  · exact embBit_nonempty (hD X hX)

/-- The **lift object** `𝒟_⊥` of Scott's category. -/
def ScottSys.lift (A : ScottSys) : ScottSys := ⟨liftTok A.sys A.ne, liftTok_nonempty A.ne⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **embedding** `|𝒟| ↪ |𝒟_⊥|`: `liftUp x = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ x}`, the image of `x`
sitting above the fresh bottom. -/
def liftUp {D : NeighborhoodSystem Str} {hD : ∀ X, D.mem X → X.Nonempty} (x : D.Element) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, x.sub hX, rfl⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [liftTokMaster_inter_embF (x.sub hX')]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, liftTokMaster_inter_embF (x.sub hX)]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embBit_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', x.up_mem hX hX' (embBit_subset.mp hsub), rfl⟩

@[simp] theorem mem_liftBot {W : Set Str} : (liftBot D hD).mem W ↔ W = liftTokMaster D := Iff.rfl

@[simp] theorem mem_liftUp {x : D.Element} {W : Set Str} :
    (liftUp (hD := hD) x).mem W ↔ W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

/-- **`f_⊥`, the action of lifting on (approximable) maps.** It carries the master to the master (so
it is strict) and a copy `0X` to `0X'` whenever `X f X'`. -/
def liftMapTok (f : ApproximableMap A.sys B.sys) :
    ApproximableMap (ScottSys.lift A).sys (ScottSys.lift B).sys where
  rel W W' :=
    ((liftTok A.sys A.ne).mem W ∧ W' = liftTokMaster B.sys) ∨
    (∃ X X', f.rel X X' ∧ W = embBit false X ∧ W' = embBit false X')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩)
    · exact hW
    · exact liftTok_mem_embF (hD := A.ne) (f.rel_dom hrel)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact liftTok_mem_embF (hD := B.ne) (f.rel_cod hrel)
  master_rel := Or.inl ⟨(ScottSys.lift A).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr ⟨X, X', hrel, hWeq, by rw [liftTokMaster_inter_embF (f.rel_cod hrel)]⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr ⟨X, X', hrel, rfl, ?_⟩
        rw [Set.inter_comm, liftTokMaster_inter_embF (f.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr ⟨X, X' ∩ X'₂, f.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((ScottSys.lift B).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZ'mem with rfl | ⟨X₃, hX₃, rfl⟩
      · exact Or.inl ⟨hZmem, rfl⟩
      · rcases hZmem with rfl | ⟨X₂, hX₂, rfl⟩
        · exact absurd (hWW nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X₂, X₃,
            f.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_embFF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit false (embBit false W))) : D.sys.mem W :=
  liftTok_mem_embF_inv (hD := D.ne)
    (oplusTok_mem_embF_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

theorem o_embTF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit true (embBit false W))) : E.sys.mem W :=
  liftTok_mem_embF_inv (hD := E.ne)
    (oplusTok_mem_embT_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

theorem o_mem_embFF {X' : Set Str} (hX' : D.sys.mem X') :
    (D.lift.oplus E.lift).sys.mem (embBit false (embBit false X')) :=
  oplusTok_mem_embF (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := D.ne) hX') (embF_ne_liftTokMaster (D := D.sys))

theorem o_mem_embTF {Y' : Set Str} (hY' : E.sys.mem Y') :
    (D.lift.oplus E.lift).sys.mem (embBit true (embBit false Y')) :=
  oplusTok_mem_embT (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := E.ne) hY') (embF_ne_liftTokMaster (D := E.sys))

/-- The forward half `|𝒟_⊥ ⊕ ℰ_⊥| → |𝒟 + ℰ|`: delete the inner `0`. -/
def toSumLift (z : (D.lift.oplus E.lift).sys.Element) : (D.sum E).sys.Element where
  mem W := W = sumTokMaster D.sys E.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false X ∧ z.mem (embBit false (embBit false X)))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true Y ∧ z.mem (embBit true (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX
    · exact sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embBit_inter, embBit_inter] at hz
        exact o_embFF_inv (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embBit_inter, embBit_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embBit_inter, embBit_inter] at hz
        exact o_embTF_inv (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embBit_inter, embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.sum E).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X'', hX'', rfl, ?_⟩)
        exact z.up_mem hzX (o_mem_embFF hX'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide) (D.ne X hX) hs)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide) (E.ne Y hY) hs)
      · refine Or.inr (Or.inr ⟨Y'', hY'', rfl, ?_⟩)
        exact z.up_mem hzY (o_mem_embTF hY'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))

@[simp] theorem toSumLift_mem_embF {z : (D.lift.oplus E.lift).sys.Element} {X : Set Str}
    (hX : D.sys.mem X) :
    (toSumLift z).mem (embBit false X) ↔ z.mem (embBit false (embBit false X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (D.ne X hX))
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toSumLift_mem_embT {z : (D.lift.oplus E.lift).sys.Element} {Y : Set Str}
    (hY : E.sys.mem Y) :
    (toSumLift z).mem (embBit true Y) ↔ z.mem (embBit true (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide) (E.ne Y hY))
    · rwa [embBit_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-- The inverse half `|𝒟 + ℰ| → |𝒟_⊥ ⊕ ℰ_⊥|`: reinstate the inner `0`. -/
def fromSumLift (s : (D.sum E).sys.Element) : (D.lift.oplus E.lift).sys.Element where
  mem W := W = sumTokMaster D.lift.sys E.lift.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false (embBit false X) ∧ s.mem (embBit false X))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true (embBit false Y) ∧ s.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact o_mem_embFF hX
    · exact o_mem_embTF hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr (Or.inl ⟨X', hX', ?_, hsX'⟩)
      rw [sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX')]
    · refine Or.inr (Or.inr ⟨Y', hY', ?_, hsY'⟩)
      rw [sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY')]
    · refine Or.inr (Or.inl ⟨X, hX, ?_, hsX⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX)]
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [embBit_inter] at hs
        exact sumTok_mem_embF_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [embBit_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y, hY, ?_, hsY⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY)]
    · exfalso
      have hs := s.inter_mem hsY hsX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [embBit_inter] at hs
        exact sumTok_mem_embT_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [embBit_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.oplus E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hV with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inl ⟨X'', hX''D, rfl, ?_⟩)
          exact s.up_mem hsX (sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX''D)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide)
            (embBit_nonempty (D.ne X hX)) hs)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide)
            (embBit_nonempty (E.ne Y hY)) hs)
      · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inr ⟨Y'', hY''E, rfl, ?_⟩)
          exact s.up_mem hsY (sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY''E)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))

@[simp] theorem fromSumLift_mem_embFF {s : (D.sum E).sys.Element} {X : Set Str} (hX : D.sys.mem X) :
    (fromSumLift s).mem (embBit false (embBit false X)) ↔ s.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective (embBit_injective heq)]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide)
        (embBit_nonempty (D.ne X hX)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromSumLift_mem_embTF {s : (D.sum E).sys.Element} {Y : Set Str} (hY : E.sys.mem Y) :
    (fromSumLift s).mem (embBit true (embBit false Y)) ↔ s.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide)
        (embBit_nonempty (E.ne Y hY)))
    · rwa [embBit_injective (embBit_injective heq)]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

theorem fromSumLift_toSumLift (z : (D.lift.oplus E.lift).sys.Element) :
    fromSumLift (toSumLift z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toSumLift_mem_embF hX).mp hs
    · exact (toSumLift_mem_embT hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X', hX'D, rfl⟩
      · exact absurd rfl hXne
      · exact Or.inr (Or.inl ⟨X', hX'D, rfl, (toSumLift_mem_embF hX'D).mpr hW⟩)
    · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
      · exact absurd rfl hYne
      · exact Or.inr (Or.inr ⟨Y', hY'E, rfl, (toSumLift_mem_embT hY'E).mpr hW⟩)

theorem lp_mem_embF {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y')) :=
  liftTok_mem_embF (hD := (D.prod E).ne) (prodTok_mem_prodTokNbhd hX' hY')

theorem lp_prod_inv {X' Y' : Set Str}
    (h : (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨A, B, hA, hB, heq⟩ := liftTok_mem_embF_inv (hD := (D.prod E).ne) h
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
  exact ⟨hA, hB⟩

theorem ot_mem_prod {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y')) :=
  otimesTok_mem_prod (liftTok_mem_embF (hD := D.ne) hX') (liftTok_mem_embF (hD := E.ne) hY')
    (embF_ne_liftTokMaster (D := D.sys)) (embF_ne_liftTokMaster (D := E.sys))

theorem ot_mem_prod_inv {X' Y' : Set Str}
    (h : (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨h1, h2⟩ := otimesTok_mem_prod_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys) h
    (embF_ne_liftTokMaster (D := D.sys))
  exact ⟨liftTok_mem_embF_inv (hD := D.ne) h1, liftTok_mem_embF_inv (hD := E.ne) h2⟩

/-- The forward half `|𝒟_⊥ ⊗ ℰ_⊥| → |(𝒟 × ℰ)_⊥|`. -/
def toLiftProd (z : (D.lift.otimes E.lift).sys.Element) : (D.prod E).lift.sys.Element where
  mem W := W = liftTokMaster (prodTok D.sys E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = embBit false (prodTokNbhd X Y) ∧
        z.mem (prodTokNbhd (embBit false X) (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact lp_mem_embF hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hzXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hzXY'⟩
      rw [liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX' hY')]
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hzXY⟩
      rw [Set.inter_comm, liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX hY)]
    · have hz := z.inter_mem hzXY hzXY'
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter] at hz
      obtain ⟨hXi, hYi⟩ := ot_mem_prod_inv (z.sub hz)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hz⟩
      rw [embBit_inter, prodTokNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.prod E).lift.sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨Z, hZ, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X'', Y'', hX'', hY'', rfl⟩ := hZ
        refine Or.inr ⟨X'', Y'', hX'', hY'', rfl, ?_⟩
        obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp (embBit_subset.mp hsub)
        exact z.up_mem hzXY (ot_mem_prod hX'' hY'')
          (prodTokNbhd_subset_iff.mpr ⟨embBit_subset.mpr hsX, embBit_subset.mpr hsY⟩)

@[simp] theorem toLiftProd_mem_embF {z : (D.lift.otimes E.lift).sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (toLiftProd z).mem (embBit false (prodTokNbhd X Y)) ↔
      z.mem (prodTokNbhd (embBit false X) (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hz⟩)
    · exact absurd h0 (embF_ne_liftTokMaster (D := prodTok D.sys E.sys))
    · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective (embBit_injective heq); exact hz
  · intro hz; exact Or.inr ⟨X, Y, hX, hY, rfl, hz⟩

/-- The inverse half `|(𝒟 × ℰ)_⊥| → |𝒟_⊥ ⊗ ℰ_⊥|`. -/
def fromLiftProd (s : (D.prod E).lift.sys.Element) : (D.lift.otimes E.lift).sys.Element where
  mem W := W = prodTokNbhd (liftTokMaster D.sys) (liftTokMaster E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = prodTokNbhd (embBit false X) (embBit false Y) ∧
        s.mem (embBit false (prodTokNbhd X Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact ot_mem_prod hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hsXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hsXY'⟩
      rw [prodTokNbhd_inter, liftTokMaster_inter_embF hX', liftTokMaster_inter_embF hY']
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hsXY⟩
      rw [Set.inter_comm, prodTokNbhd_inter, liftTokMaster_inter_embF hX,
        liftTokMaster_inter_embF hY]
    · have hs := s.inter_mem hsXY hsXY'
      rw [embBit_inter, prodTokNbhd_inter] at hs
      obtain ⟨hXi, hYi⟩ := lp_prod_inv (s.sub hs)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hs⟩
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.otimes E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨U, V, hU, hV, hUne, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hU with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hUne
        · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hVne
          · refine Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, ?_⟩
            obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
            exact s.up_mem hsXY (lp_mem_embF hX''D hY''E)
              (embBit_subset.mpr (prodTokNbhd_subset_iff.mpr
                ⟨embBit_subset.mp hsX, embBit_subset.mp hsY⟩))

@[simp] theorem fromLiftProd_mem_prod {s : (D.prod E).lift.sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (fromLiftProd s).mem (prodTokNbhd (embBit false X) (embBit false Y)) ↔
      s.mem (embBit false (prodTokNbhd X Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hs⟩)
    · obtain ⟨hX0, -⟩ := prodTokNbhd_injective h0
      exact absurd hX0 (embF_ne_liftTokMaster (D := D.sys))
    · obtain ⟨hXe, hYe⟩ := prodTokNbhd_injective heq
      rw [embBit_injective hXe, embBit_injective hYe]; exact hs
  · intro hs; exact Or.inr ⟨X, Y, hX, hY, rfl, hs⟩

theorem fromLiftProd_toLiftProd (z : (D.lift.otimes E.lift).sys.Element) :
    fromLiftProd (toLiftProd z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toLiftProd_mem_embF hX hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
      · exact absurd rfl hXne
      · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hYne
        · exact Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, (toLiftProd_mem_embF hX''D hY''E).mpr hW⟩

theorem toLiftProd_fromLiftProd (s : (D.prod E).lift.sys.Element) :
    toLiftProd (fromLiftProd s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromLiftProd_mem_prod hX hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨Z, hZ, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, Y, hX, hY, rfl⟩ := hZ
      exact Or.inr ⟨X, Y, hX, hY, rfl, (fromLiftProd_mem_prod hX hY).mpr hW⟩

/-- The order-isomorphism `|𝒟_⊥ ⊗ ℰ_⊥| ≃o |(𝒟 × ℰ)_⊥|`. -/
def liftProdEquiv : (D.lift.otimes E.lift).sys.Element ≃o (D.prod E).lift.sys.Element where
  toFun := toLiftProd
  invFun := fromLiftProd
  left_inv := fromLiftProd_toLiftProd
  right_inv := toLiftProd_fromLiftProd
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hXne
        · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hYne
          · exact (toLiftProd_mem_embF hX''D hY''E).mp
              (h _ ((toLiftProd_mem_embF hX''D hY''E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, Y, hX, hY, rfl, h _ hzXY⟩

theorem toSumLift_fromSumLift (s : (D.sum E).sys.Element) :
    toSumLift (fromSumLift s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromSumLift_mem_embFF hX).mp hs
    · exact (fromSumLift_mem_embTF hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromSumLift_mem_embFF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromSumLift_mem_embTF hY).mpr hW⟩)

/-- The order-isomorphism `|𝒟_⊥ ⊕ ℰ_⊥| ≃o |𝒟 + ℰ|`. -/
def sumLiftEquiv : (D.lift.oplus E.lift).sys.Element ≃o (D.sum E).sys.Element where
  toFun := toSumLift
  invFun := fromSumLift
  left_inv := fromSumLift_toSumLift
  right_inv := toSumLift_fromSumLift
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X', hX'D, rfl⟩
        · exact absurd rfl hXne
        · exact (toSumLift_mem_embF hX'D).mp (h _ ((toSumLift_mem_embF hX'D).mpr hW))
      · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
        · exact absurd rfl hYne
        · exact (toSumLift_mem_embT hY'E).mp (h _ ((toSumLift_mem_embT hY'E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **unlift** of an element that lies above the fresh bottom (i.e. contains `0Δ`): the
`𝒟`-element `{X ∣ 0X ∈ z}`. -/
def unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) : D.Element where
  mem X := z.mem (embBit false X)
  sub := fun hX => liftTok_mem_embF_inv (z.sub hX)
  master_mem := hz
  inter_mem := by
    intro X X' hX hX'
    have hz' := z.inter_mem hX hX'
    rwa [embBit_inter] at hz'
  up_mem := by
    intro X Y hX hY hXY
    exact z.up_mem hX (liftTok_mem_embF hY) (embBit_subset.mpr hXY)

/-- `liftBot` is the least element of `𝒟_⊥`. -/
theorem liftBot_le (z : (liftTok D hD).Element) : liftBot D hD ≤ z := by
  rintro W rfl; exact z.master_mem

/-- The fresh bottom is *strictly* below every lifted element. -/
theorem liftBot_lt_liftUp (x : D.Element) : liftBot D hD < liftUp (hD := hD) x := by
  refine lt_of_le_of_ne (liftBot_le _) (fun heq => ?_)
  have hmem : (liftBot D hD).mem (embBit false D.master) := by
    rw [heq]; exact Or.inr ⟨D.master, x.master_mem, rfl⟩
  exact embF_ne_liftTokMaster hmem

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

/-- **`(g ∘ f)_⊥ = g_⊥ ∘ f_⊥`.** -/
theorem liftMapTok_comp (f : ApproximableMap A.sys B.sys) (g : ApproximableMap B.sys C.sys) :
    liftMapTok (g.comp f) = (liftMapTok g).comp (liftMapTok f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨liftTokMaster B.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(ScottSys.lift B).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr ⟨X, X', hf, rfl, rfl⟩, Or.inr ⟨X', X'', hg, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩
      · exact Or.inl ⟨liftTok_mem_embF (hD := A.ne) (f.rel_dom hf), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩

/-- **`(I_𝒟)_⊥ = I_{𝒟_⊥}`.** -/
theorem liftMapTok_id : liftMapTok (idMap A.sys) = idMap (ScottSys.lift A).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (ScottSys.lift A).sys.master_mem, (ScottSys.lift A).sys.sub_master hW⟩
    · exact ⟨liftTok_mem_embF (hD := A.ne) hX, liftTok_mem_embF (hD := A.ne) hX',
        embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩
      · exact absurd (hsub nil_mem_liftTokMaster) nil_not_mem_embBit
      · exact Or.inr ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩

/-- **`f_⊥` is strict** for *any* `f`: the master `Λ`-bearing input relates only to the master. -/
theorem liftMapTok_isStrict (f : ApproximableMap A.sys B.sys) : IsStrict (liftMapTok f) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩)
  · rfl
  · have hnil : ([] : Str) ∈ embBit false X := by
      rw [← heq]; exact nil_mem_liftTokMaster
    exact absurd hnil nil_not_mem_embBit

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_master : (liftTok D hD).mem (liftTokMaster D) := Or.inl rfl

/-- `liftUp` is an order embedding: `liftUp x ⊑ liftUp y ↔ x ⊑ y`. -/
theorem liftUp_le_liftUp_iff {x y : D.Element} :
    liftUp (hD := hD) x ≤ liftUp (hD := hD) y ↔ x ≤ y := by
  constructor
  · intro h X hX
    have hmem := h (embBit false X) (Or.inr ⟨X, hX, rfl⟩)
    rcases hmem with h0 | ⟨X', hX', heq⟩
    · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rw [embBit_injective heq]; exact hX'
  · rintro h W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h X hX, rfl⟩

theorem liftUp_unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) :
    liftUp (hD := hD) (unlift z hz) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl⟩)
    · exact z.master_mem
    · exact hX
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, hW, rfl⟩

/-- **Exercise 6.26 — "describe in terms of elements".** Every element of `𝒟_⊥` is either the fresh
bottom or a lifted `𝒟`-element: `|𝒟_⊥| ≅ |𝒟|_⊥`. (`Prop`-level; the case split on "does `z` contain
`0Δ`?" uses excluded middle — the only non-constructive step in this module.) -/
theorem eq_liftBot_or_exists_liftUp (z : (liftTok D hD).Element) :
    z = liftBot D hD ∨ ∃ x : D.Element, z = liftUp (hD := hD) x := by
  by_cases hz : z.mem (embBit false D.master)
  · exact Or.inr ⟨unlift z hz, (liftUp_unlift z hz).symm⟩
  · refine Or.inl ?_
    apply NeighborhoodSystem.Element.ext
    intro W
    constructor
    · intro hW
      rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
      · rfl
      · exact absurd
          (z.up_mem hW (liftTok_mem_embF D.master_mem) (embBit_subset.mpr (D.sub_master hX))) hz
    · rintro rfl; exact z.master_mem

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- **Exercise 6.26 — `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`.** Coalescing the fresh bottoms of the two lifts
reproduces the separated sum. -/
theorem lift_oplus_lift_iso_sum :
    (D.lift.oplus E.lift).sys ≅ᴰ (D.sum E).sys := ⟨sumLiftEquiv⟩

/-- **Exercise 6.26 — `𝒟_⊥ ⊗ ℰ_⊥ ≅ (𝒟 × ℰ)_⊥`** (the answer to Scott's `??`). The smash product of
two lifts is the lift of the product. -/
theorem lift_otimes_lift_iso_lift_prod :
    (D.lift.otimes E.lift).sys ≅ᴰ (D.prod E).lift.sys := ⟨liftProdEquiv⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_626 : And
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys) :=
  @And.intro
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys)
  (@And.intro
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys)
    @DomainTheory.NeighbourhoodSystems.Exercise619.eq_liftBot_or_exists_liftUp
    @DomainTheory.NeighbourhoodSystems.Exercise619.lift_oplus_lift_iso_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise619.lift_otimes_lift_iso_lift_prod
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The injection `i : 𝒟 → 𝒟 × ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟×ℰ ∧ (X,Δ₁) ⊆ W`. -/
def fstInj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap D₀ (prodTok D₀ D₁) where
  rel X W := D₀.mem X ∧ (prodTok D₀ D₁).mem W ∧ prodTokNbhd X D₁.master ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (prodTok D₀ D₁).master_mem, subset_rfl⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (prodTok D₀ D₁).inter_mem hW hW' (prodTok_mem_prodTokNbhd hX D₁.master_mem)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((prodTokNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩).trans hsub).trans hWW'⟩

/-- The projection `j : 𝒟 × ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟×ℰ ∧ X ∈ 𝒟 ∧ W ⊆ (X,Δ₁)`. -/
def fstProj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap (prodTok D₀ D₁) D₀ where
  rel W X := (prodTok D₀ D₁).mem W ∧ D₀.mem X ∧ W ⊆ prodTokNbhd X D₁.master
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prodTok D₀ D₁).master_mem, D₀.master_mem, subset_rfl⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    obtain ⟨A, B, hA, hB, rfl⟩ := hW
    have hAX : A ⊆ X := (prodTokNbhd_subset_iff.mp hsub).1
    have hAX' : A ⊆ X' := (prodTokNbhd_subset_iff.mp hsub').1
    exact ⟨prodTok_mem_prodTokNbhd hA hB, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
      prodTokNbhd_subset_iff.mpr ⟨Set.subset_inter hAX hAX', D₁.sub_master hB⟩⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩))⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Element-level inclusion `|𝒟 →⊥ ℰ| → |𝒟 → ℰ|`. -/
def incl (φ : (strictFun V₀ V₁).Element) : (funSpace V₀ V₁).Element :=
  toFilter (toStrictMap φ).1

theorem incl_mono : Monotone (incl (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab M hM
  obtain ⟨hMmem, haM⟩ := hM
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : (toStrictMap a).1 ≤ (toStrictMap b).1 := (strictFunEquiv V₀ V₁).monotone hab
  exact hle p.1 p.2 (haM p hp)

/-- The inclusion `i : 𝒟 →⊥ ℰ ↪ 𝒟 → ℰ`. -/
def inclMap : ApproximableMap (strictFun V₀ V₁) (funSpace V₀ V₁) :=
  ofMono (fun _ hW => incl ((strictFun V₀ V₁).principal hW))
    (fun _ _ hW hW' hW'W => incl_mono (((strictFun V₀ V₁).principal_le_iff hW hW').mpr hW'W))

end Part5

/-- The left-copy generator: `0X` for proper `X`, the shared bottom `sumTokMaster` for `X = Δ₀`. The
set-builder `{w ∣ w ∈ sumTokMaster ∧ X = Δ₀}` keeps the *definition* choice-free. -/
def leftN (D₀ D₁ : NeighborhoodSystem Str) (X : Set Str) : Set Str :=
  embBit false X ∪ {w | w ∈ sumTokMaster D₀ D₁ ∧ X = D₀.master}

theorem X_eq_master_of_embT_subset_leftN {B X : Set Str} (hB : B.Nonempty)
    (h : embBit true B ⊆ leftN D₀ D₁ X) : X = D₀.master := by
  obtain ⟨σ, hσ⟩ := hB
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', -⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; exact absurd hw'.1 (by decide)
  · exact hXm

theorem X_eq_master_of_nil_mem_leftN {X : Set Str} (h : ([] : Str) ∈ leftN D₀ D₁ X) :
    X = D₀.master := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h nil_not_mem_embBit
  · exact h

theorem embF_subset_leftN {X : Set Str} : embBit false X ⊆ leftN D₀ D₁ X :=
  Set.subset_union_left

theorem leftN_master : leftN D₀ D₁ D₀.master = sumTokMaster D₀ D₁ := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨hw, -⟩)
    · exact embF_subset_sumTokMaster D₀.master_mem hw
    · exact hw
  · exact fun w hw => Or.inr ⟨hw, rfl⟩

theorem leftN_proper {X : Set Str} (hne : X ≠ D₀.master) : leftN D₀ D₁ X = embBit false X := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨-, hXm⟩)
    · exact hw
    · exact absurd hXm hne
  · exact embF_subset_leftN

/-- The **only** classical step in Exercise 6.27: `leftN X` is an `𝒟 ⊕ ℰ`-neighbourhood. The proof
splits on the (undecidable for arbitrary `X`) test `X = Δ₀`. -/
theorem oplus_mem_leftN {X : Set Str} (hX : D₀.mem X) :
    (oplusTok D₀ D₁ h₀ h₁).mem (leftN D₀ D₁ X) := by
  by_cases h : X = D₀.master
  · rw [h, leftN_master]; exact (oplusTok D₀ D₁ h₀ h₁).master_mem
  · rw [leftN_proper h]; exact oplusTok_mem_embF hX h

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Strictification of a map** (on relations): keep `f` but force the master input to the master
output. The resulting map is strict, lies below `f`, and is the identity on strict maps. -/
def strictifyMap (g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Y := g.rel X Y ∧ (X = V₀.master → Y = V₁.master)
  rel_dom h := g.rel_dom h.1
  rel_cod h := g.rel_cod h.1
  master_rel := ⟨g.master_rel, fun _ => rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hg, hs⟩ ⟨hg', hs'⟩
    exact ⟨g.inter_right hg hg', fun hX => by rw [hs hX, hs' hX, Set.inter_self]⟩
  mono := by
    rintro X X' Y Y' ⟨hg, hs⟩ hX'X hYY' hX' hY'
    refine ⟨g.mono hg hX'X hYY' hX' hY', fun hX'm => ?_⟩
    have hX : V₀.mem X := g.rel_dom hg
    have hXm : X = V₀.master := Set.Subset.antisymm (V₀.sub_master hX) (hX'm ▸ hX'X)
    exact Set.Subset.antisymm (V₁.sub_master hY') ((hs hXm) ▸ hYY')

theorem strictifyMap_isStrict (g : ApproximableMap V₀ V₁) : IsStrict (strictifyMap g) :=
  fun _ h => h.2 rfl

/-- The strictification as an element of the *strict* function space's token type. -/
def strictify (g : ApproximableMap V₀ V₁) : StrictMap V₀ V₁ := ⟨strictifyMap g, strictifyMap_isStrict g⟩

/-- Element-level strictification `|𝒟 → ℰ| → |𝒟 →⊥ ℰ|`. -/
def strct (ψ : (funSpace V₀ V₁).Element) : (strictFun V₀ V₁).Element :=
  toStrictFilter (strictify (toApproxMap ψ))

theorem strct_mono : Monotone (strct (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab W hW
  obtain ⟨hWmem, haW⟩ := hW
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : toApproxMap a ≤ toApproxMap b := (funSpaceEquiv V₀ V₁).monotone hab
  exact ⟨hle p.1 p.2 (haW p hp).1, (haW p hp).2⟩

/-- The strictification retraction `j : 𝒟 → ℰ → 𝒟 →⊥ ℰ`. -/
def strctMap : ApproximableMap (funSpace V₀ V₁) (strictFun V₀ V₁) :=
  ofMono (fun _ hM => strct ((funSpace V₀ V₁).principal hM))
    (fun _ _ hM hM' hM'M => strct_mono (((funSpace V₀ V₁).principal_le_iff hM hM').mpr hM'M))

end Part5

theorem subset_of_embF_subset_leftN {A X : Set Str} (hA : A ⊆ D₀.master)
    (h : embBit false A ⊆ leftN D₀ D₁ X) : A ⊆ X := by
  intro σ hσ
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', hw'X⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; rw [hw'.2]; exact hw'X
  · rw [hXm]; exact hA hσ

theorem leftN_subset_iff {X X' : Set Str} (hX : D₀.mem X) (hX' : D₀.mem X') :
    leftN D₀ D₁ X ⊆ leftN D₀ D₁ X' ↔ X ⊆ X' := by
  constructor
  · intro h
    exact subset_of_embF_subset_leftN (D₀.sub_master hX) (embF_subset_leftN.trans h)
  · intro hXX'
    rintro w (⟨w', rfl, hw'⟩ | ⟨hw, hXm⟩)
    · exact embF_subset_leftN ⟨w', rfl, hXX' hw'⟩
    · exact Or.inr ⟨hw, Set.Subset.antisymm (D₀.sub_master hX') (hXm ▸ hXX')⟩

/-- The injection `i : 𝒟 → 𝒟 ⊕ ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟⊕ℰ ∧ leftN X ⊆ W`. -/
def inlInj : ApproximableMap D₀ (oplusTok D₀ D₁ h₀ h₁) where
  rel X W := D₀.mem X ∧ (oplusTok D₀ D₁ h₀ h₁).mem W ∧ leftN D₀ D₁ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (oplusTok D₀ D₁ h₀ h₁).master_mem, leftN_master.le⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (oplusTok D₀ D₁ h₀ h₁).inter_mem hW hW' (oplus_mem_leftN hX)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((leftN_subset_iff hX' hX).mpr hX'X).trans (hsub.trans hWW')⟩

/-- The projection `j : 𝒟 ⊕ ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟⊕ℰ ∧ X ∈ 𝒟 ∧ W ⊆ leftN X`. -/
def inlProj : ApproximableMap (oplusTok D₀ D₁ h₀ h₁) D₀ where
  rel W X := (oplusTok D₀ D₁ h₀ h₁).mem W ∧ D₀.mem X ∧ W ⊆ leftN D₀ D₁ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(oplusTok D₀ D₁ h₀ h₁).master_mem, D₀.master_mem, leftN_master.ge⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    rcases hW with rfl | ⟨A, hA, hAne, rfl⟩ | ⟨B, hB, hBne, rfl⟩
    · have hXm := X_eq_master_of_nil_mem_leftN (hsub nil_mem_sumTokMaster)
      have hX'm := X_eq_master_of_nil_mem_leftN (hsub' nil_mem_sumTokMaster)
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨Or.inl rfl, D₀.master_mem, leftN_master.ge⟩
    · have hAX : A ⊆ X := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub
      have hAX' : A ⊆ X' := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub'
      exact ⟨oplusTok_mem_embF hA hAne, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
        (embBit_subset.mpr (Set.subset_inter hAX hAX')).trans embF_subset_leftN⟩
    · have hXm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub
      have hX'm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub'
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨oplusTok_mem_embT hB hBne, D₀.master_mem, by
        rw [leftN_master]; exact embT_subset_sumTokMaster hB⟩
  mono := by
    rintro W W' X X' ⟨_, hX, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans ((leftN_subset_iff hX hX').mpr hXX'))⟩

/-- A concrete two-point domain over `{0,1}*`: neighbourhoods `Set.univ` (`= ⊥`) and `{[]}`. -/
def twoPt : NeighborhoodSystem Str where
  mem X := X = Set.univ ∨ X = {[]}
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro X (rfl | rfl)
    · exact subset_rfl
    · exact Set.subset_univ _
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [Set.univ_inter]; exact Or.inr rfl
    · rw [Set.inter_univ]; exact Or.inr rfl
    · rw [Set.inter_self]; exact Or.inr rfl

/-- The one-point unit domain `𝟙` over `{0,1}*` (only neighbourhood `{[]}`). -/
def unitPt : NeighborhoodSystem Str := (singletonSys ({[]} : Set Str) ⟨[], rfl⟩).sys

theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

end Exercise627
end
end DomainTheory.NeighbourhoodSystems
end
