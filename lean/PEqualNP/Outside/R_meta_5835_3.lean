import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.R_meta_5835_3
    (monotone : let step := fun (w : List (BitVec 27)) (g : Fin 3 × ℕ × ℕ) =>
      let a := w.getD g.2.1 0
      let b := w.getD g.2.2 0
      w ++ [if g.1 = 0 then a &&& b else if g.1 = 1 then a ||| b else ~~~a]
      ∀ A : List (Fin 3 × ℕ × ℕ), A.length ≤ 16 → (∀ g ∈ A, g.1 ≠ 2) →
        let W := A.foldl step [0,134217727,78959277,55258451,67371142,26740244,4333592,16910624,1331264,7963008,106962432,125952000]
        ∀ i j : ℕ, let a := W.getD i 0; let b := W.getD j 0
          a &&& b ≠ 131071 ∧ a ||| b ≠ 131071)
    (inverting : let pack := fun f : Fin 768 → Bool => (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
      let mask := fun r : Fin 768 => 4 * (r.val / 3) + r.val % 3 + 1
      let step := fun (w : List (BitVec 768)) (g : Fin 3 × ℕ × ℕ) =>
      let a := w.getD g.2.1 0
      let b := w.getD g.2.2 0
      w ++ [if g.1 = 0 then a &&& b else if g.1 = 1 then a ||| b else ~~~a]
      ∀ (P Q : List (Fin 3 × ℕ × ℕ)) (j : ℕ), P.length + Q.length ≤ 16 →
        (∀ g ∈ P, g.1 ≠ 2) →
        let W := P.foldl step ([0, ~~~0] ++ List.ofFn (fun i : Fin 10 => pack (fun r => (mask r).testBit i.val)))
        pack (fun r => !([1, 2, 5, 9, 10, 18, 34, 42, 50, 65, 69, 73, 129, 130, 137, 138, 146, 193, 201, 257, 258, 261, 274, 385, 386, 402, 513, 514, 517, 521, 522, 546, 554, 769, 770, 773] : List ℕ).contains (mask r)) ∉
          Q.foldl step (W ++ [~~~(W.getD j 0)])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))) = Bool.true ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C fan small
  by_contra! fail
  let target := (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)))
  let opcode (op : GateOp) : Fin 3 :=
    if op.eval [true] then (if op.eval [] then 0 else 1) else 2
  let enc (g : Gate) : Fin 3 × ℕ × ℕ :=
    let a := g.inputs.head?.elim (if opcode g.op = 0 then 1 else 0) (· + 2)
    (opcode g.op, a, g.inputs[1]?.elim a (· + 2))
  let step {n : ℕ} := fun (w : List (BitVec n)) (g : Fin 3 × ℕ × ℕ) =>
      let a := w.getD g.2.1 0
      let b := w.getD g.2.2 0
      w ++ [if g.1 = 0 then a &&& b else if g.1 = 1 then a ||| b else ~~~a]
  let advance (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have sim {n : ℕ} (r : Fin n) (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ C.gates)
      (w : List (BitVec n)) (bs : List Bool)
      (init : w.map (fun v => v.getLsbD r.val) = [false,true] ++ bs) :
      ((gs.map enc).foldl step w).map (fun v => v.getLsbD r.val) =
        [false,true] ++ gs.foldl advance bs := by
    induction gs generalizing w bs with
    | nil => exact init
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih (fun a ha => sub a (List.mem_cons_of_mem _ ha))
      have rd (k : ℕ) : (w.getD k 0).getLsbD r.val = ([false,true] ++ bs).getD k false := by
        rw [← init]
        have eq := List.getD_map w (0 : BitVec n) (n := k) (fun v => v.getLsbD r.val)
        simpa using eq.symm
      obtain ⟨op,sz⟩ := fan g (sub g List.mem_cons_self)
      rcases g with ⟨kind,ls⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      change ls.length ≤ 2 at sz
      have casesL : ls = [] ∨ (∃ a, ls = [a]) ∨ (∃ a b, ls = [a,b]) := by
        rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨a,rfl⟩)
        · exact Or.inr (Or.inr ⟨a,b,rfl⟩)
        · simp at sz
      have aa (ls : List Bool) : GateOp.and.eval ls = ls.all id := rfl
      have oo (ls : List Bool) : GateOp.or.eval ls = ls.any id := rfl
      have nn (ls : List Bool) : GateOp.not.eval ls = !(ls.headD false) := rfl
      simp [r.isLt] at init rd
      rcases casesL with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ <;>
        rcases op with rfl | rfl | rfl <;>
        simp [step,advance,enc,opcode,aa,oo,nn,init,rd,r.isLt,List.append_assoc,
              List.getD_cons_succ, Nat.add_assoc]
  have result {n} (r : Fin n) (roots : List (BitVec n)) (x : Fin 10 → Bool)
      (h : roots.map (fun v => v.getLsbD r.val) = [false,true] ++ List.ofFn x)
      (prom : (x 0 || x 1) = true) :
      (((C.gates.map enc).foldl step roots).getD (C.output + 2) 0).getLsbD r.val = target x := by
    have simr := sim r C.gates (fun _ h => h) roots (List.ofFn x) h
    have lookup := congrArg (fun l : List Bool => l.getD (C.output+2) false) simr
    have eq := List.getD_map ((C.gates.map enc).foldl step roots) (0 : BitVec n)
      (n := C.output+2) (fun v => v.getLsbD r.val)
    change (((C.gates.map enc).foldl step roots).map _).getD (C.output+2) false = _ at lookup
    rw [← (show (0 : BitVec n).getLsbD r.val = false by simp), eq] at lookup
    have hz : (0 : BitVec n).getLsbD r.val = false := by simp
    rw [hz] at lookup
    exact lookup.trans (fail x prom)
  let prog := C.gates.map enc
  have size : prog.length ≤ 17 := by
    simpa only [prog,List.length_map] using (show C.gates.length ≤ 17 from small)
  by_cases mono : ∀ g ∈ prog, g.1 ≠ 2
  · let rows : List ℕ := [3, 6, 13, 17, 26, 33, 66, 133, 162, 265, 266, 290, 321, 530, 577, 641, 642, 50, 69, 138, 201, 385, 402, 521, 554, 770, 773]
    let roots : List (BitVec 27) := [0,134217727,78959277,55258451,67371142,26740244,4333592,16910624,1331264,7963008,106962432,125952000]
    let row (r : Fin 27) (j : Fin 10) := (rows.getD r.val 0).testBit j.val
    have chart : ∀ r : Fin 27,
        roots.map (fun v => v.getLsbD r.val) = [false,true] ++ List.ofFn (row r) ∧
        (row r 0 || row r 1) = true ∧ target (row r) = (131071 : BitVec 27).getLsbD r.val := by
      decide +kernel
    have hit : (prog.foldl step roots).getD (C.output+2) 0 = 131071 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let r : Fin 27 := ⟨i,hi⟩
      exact (result r roots (row r) (chart r).1 (chart r).2.1).trans (chart r).2.2
    have excludes (A : List (Fin 3 × ℕ × ℕ)) (bound : A.length ≤ 16)
        (ao : ∀ g ∈ A, g.1 ≠ 2) (i j : ℕ) :
        let W := A.foldl step roots
        (W.getD i 0 &&& W.getD j 0 ≠ 131071) ∧ (W.getD i 0 ||| W.getD j 0 ≠ 131071) :=
      monotone A bound ao i j
    by_cases hshort : prog.length ≤ 16
    · exact (excludes prog hshort mono (C.output+2) (C.output+2)).1 (by rw [hit]; decide)
    obtain ⟨A,g,split⟩ : ∃ A g, prog = A ++ [g] := by
      obtain ⟨A,g,he⟩ := List.eq_nil_or_concat' prog |>.resolve_left (fun he => by simp [he] at hshort)
      exact ⟨A,g,he⟩
    have bound : A.length ≤ 16 := by rw [split] at size; simp at size; omega
    have ao : ∀ t ∈ A, t.1 ≠ 2 := fun t ht => mono t (split ▸ List.mem_append_left [g] ht)
    have go : g.1 ≠ 2 := mono g (split ▸ List.mem_append_right A (by simp))
    let W := A.foldl step roots
    rw [split,List.foldl_append] at hit
    change (W ++ [_]).getD (C.output+2) 0 = 131071 at hit
    by_cases early : C.output+2 < W.length
    · rw [List.getD_append _ _ _ _ early] at hit
      exact (excludes A bound ao (C.output+2) (C.output+2)).1 (by change W.getD _ _ &&& W.getD _ _ = _; rw [hit]; decide)
    rw [List.getD_append_right _ _ _ _ (by omega)] at hit
    cases he : C.output+2-W.length with
    | zero =>
      rw [he] at hit
      have choose := excludes A bound ao g.2.1 g.2.2
      rcases show g.1 = 0 ∨ g.1 = 1 by omega with h|h
      · exact choose.1 (by simpa [step,h,W] using hit)
      · exact choose.2 (by simpa [step,h,W] using hit)
    | succ k => simp [he] at hit
  · push Not at mono
    have cut (L : List (Fin 3 × ℕ × ℕ)) (h : ∃ g ∈ L, g.1 = 2) :
        ∃ P g Q, L = P ++ g :: Q ∧ (∀ t ∈ P, t.1 ≠ 2) ∧ g.1 = 2 := by
      induction L with
      | nil => simp at h
      | cons g L ih =>
        by_cases hfirst : g.1 = 2
        · exact ⟨[],g,L,rfl,by simp,hfirst⟩
        have tail : ∃ t ∈ L, t.1 = 2 := by simpa [hfirst] using h
        obtain ⟨P,t,Q,he,hm,ht⟩ := ih tail
        exact ⟨g::P,t,Q,by simp [he],by simpa using And.intro hfirst hm,ht⟩
    obtain ⟨P,g,Q,split,pre,inv⟩ := cut prog mono
    have bound : P.length + Q.length ≤ 16 := by rw [split] at size; simp at size; omega
    let pack := fun f : Fin 768 → Bool => (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
    let mask := fun r : Fin 768 => 4 * (r.val / 3) + r.val % 3 + 1
    let row (r : Fin 768) (j : Fin 10) := (mask r).testBit j.val
    let roots : List (BitVec 768) := [0, ~~~0] ++ List.ofFn (fun i : Fin 10 => pack (fun r => (mask r).testBit i.val))
    let negs := ([1, 2, 5, 9, 10, 18, 34, 42, 50, 65, 69, 73, 129, 130, 137, 138, 146, 193, 201, 257, 258, 261, 274, 385, 386, 402, 513, 514, 517, 521, 522, 546, 554, 769, 770, 773] : List ℕ)
    let wanted := pack (fun r => !negs.contains (mask r))
    have bit (f : Fin 768 → Bool) (r : Fin 768) : (pack f).getLsbD r.val = f r := by
      simp only [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
      simp [r.isLt]
    have init (r : Fin 768) : roots.map (fun v => v.getLsbD r.val) = [false,true] ++ List.ofFn (row r) := by
      simp only [roots,List.map_append,List.map_cons,List.map_nil,BitVec.getLsbD_not,BitVec.getLsbD_zero,decide_eq_true r.isLt,Bool.not_false,Bool.and_true,List.map_ofFn]
      apply congrArg₂ List.append
      · have hz : (0 : BitVec 768).getLsbD r.val = false := by simp
        rw [hz]; rfl
      · apply congrArg List.ofFn
        funext j
        exact bit _ r
    have chart : ∀ r : Fin 768, (row r 0 || row r 1) = true ∧
        target (row r) = !([1, 2, 5, 9, 10, 18, 34, 42, 50, 65, 69, 73, 129, 130, 137, 138, 146, 193, 201, 257, 258, 261, 274, 385, 386, 402, 513, 514, 517, 521, 522, 546, 554, 769, 770, 773] : List ℕ).contains (mask r) := by decide +kernel
    let V := prog.foldl step roots
    have hit : V.getD (C.output+2) 0 = wanted := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let r : Fin 768 := ⟨i,hi⟩
      exact (result r roots (row r) (init r) (chart r).1).trans (by rw [show wanted.getLsbD i = _ from bit (fun r => !negs.contains (mask r)) r]; exact (chart r).2)
    have nz : wanted ≠ 0 := by
      intro e
      have eq := congrArg (fun v : BitVec 768 => v.getLsbD 2) e
      change wanted.getLsbD (2 : Fin 768).val = false at eq
      rw [show wanted.getLsbD (2 : Fin 768).val = true from (bit (fun r => !negs.contains (mask r)) 2).trans (by decide)] at eq
      contradiction
    have live : C.output+2 < V.length := by
      by_contra! h
      rw [List.getD_eq_default _ _ h] at hit
      exact nz hit.symm
    have mem : wanted ∈ V := by
      rw [← hit,List.getD_eq_getElem _ _ live]
      exact List.getElem_mem ..
    have no := inverting P Q g.2.1 bound pre
    apply no
    simpa only [V,split,List.foldl_append,List.foldl_cons,step,inv,show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide,if_false] using mem
