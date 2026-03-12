(******************************************************************************)
(*                                                                            *)
(*                       Thresholded OOK Run Semantics                        *)
(*                                                                            *)
(*     Formalizes thresholded OOK traces from raw IQ window energies.         *)
(*     Proves burst detection, run flattening, onset/offset soundness,        *)
(*     and normalized pulse-gap classification across timing scales.          *)
(*                                                                            *)
(*     "The true logic of this world is the calculus of probabilities."       *)
(*     - James Clerk Maxwell, 1850                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 11, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)


From Stdlib Require Import List Bool Arith Lia.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.

Require Extraction.

Import ListNotations.

Definition Window := bool.
Definition Trace := list Window.

Fixpoint count_active (xs : Trace) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => (if x then 1 else 0) + count_active xs'
  end.

Fixpoint take (n : nat) (xs : Trace) : Trace :=
  match n, xs with
  | O, _ => []
  | S n', [] => []
  | S n', x :: xs' => x :: take n' xs'
  end.

Fixpoint drop (n : nat) (xs : Trace) : Trace :=
  match n, xs with
  | O, _ => xs
  | S n', [] => []
  | S n', _ :: xs' => drop n' xs'
  end.

Definition window_active_count (span : nat) (xs : Trace) : nat :=
  count_active (take span xs).

Definition dense_window (span min_active : nat) (xs : Trace) : bool :=
  Nat.leb min_active (window_active_count span xs).

Fixpoint first_dense_window (span min_active : nat) (xs : Trace) : option nat :=
  match xs with
  | [] =>
      if dense_window span min_active [] then Some 0 else None
  | _ :: xs' =>
      if dense_window span min_active xs then
        Some 0
      else
        match first_dense_window span min_active xs' with
        | Some idx => Some (S idx)
        | None => None
        end
  end.

Definition has_dense_window (span min_active : nat) (xs : Trace) : bool :=
  match first_dense_window span min_active xs with
  | Some _ => true
  | None => false
  end.

Fixpoint first_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      if x then
        Some 0
      else
        match first_true xs' with
        | Some idx => Some (S idx)
        | None => None
        end
  end.

Fixpoint last_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      match last_true xs' with
      | Some idx => Some (S idx)
      | None => if x then Some 0 else None
      end
  end.

Lemma dense_window_true :
  forall span min_active xs,
    dense_window span min_active xs = true ->
    min_active <= window_active_count span xs.
Proof.
  intros span min_active xs H.
  unfold dense_window in H.
  apply Nat.leb_le.
  exact H.
Qed.

Lemma take_app_prefix :
  forall n xs ys,
    n <= length xs ->
    take n (xs ++ ys) = take n xs.
Proof.
  induction n as [|n IH]; intros xs ys Hlen.
  - reflexivity.
  - destruct xs as [|x xs']; simpl in *.
    + lia.
    + f_equal.
      apply IH.
      lia.
Qed.

Lemma take_drop :
  forall n xs,
    take n xs ++ drop n xs = xs.
Proof.
  induction n as [|n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Theorem first_dense_window_sound :
  forall span min_active xs idx,
    first_dense_window span min_active xs = Some idx ->
    idx <= length xs /\
    min_active <= window_active_count span (drop idx xs).
Proof.
  induction xs as [|x xs IH]; intros idx Hscan; simpl in Hscan.
  - destruct (dense_window span min_active []) eqn:Hdense.
    + inversion Hscan; subst.
      split.
      * lia.
      * apply dense_window_true.
        exact Hdense.
    + discriminate.
  - destruct (dense_window span min_active (x :: xs)) eqn:Hdense.
    + inversion Hscan; subst.
      split.
      * lia.
      * apply dense_window_true.
        exact Hdense.
    + destruct (first_dense_window span min_active xs) eqn:Htail.
      * inversion Hscan; subst.
        specialize (IH n eq_refl) as [Hidx Hcount].
        split.
        -- simpl.
           lia.
        -- simpl.
           exact Hcount.
      * discriminate.
Qed.

Theorem first_dense_window_complete_from_suffix :
  forall prefix suffix span min_active,
    min_active <= window_active_count span suffix ->
    exists idx,
      first_dense_window span min_active (prefix ++ suffix) = Some idx.
Proof.
  induction prefix as [|x prefix IH]; intros suffix span min_active Hcount.
  - destruct suffix as [|w ws].
    + assert (Hzero : window_active_count span [] = 0).
      {
        unfold window_active_count.
        destruct span; reflexivity.
      }
      rewrite Hzero in Hcount.
      destruct min_active as [|min_active'].
      * simpl.
        eexists.
        reflexivity.
      * exfalso.
        lia.
    + simpl.
      assert (Hdense : dense_window span min_active (w :: ws) = true).
      {
        unfold dense_window.
        apply Nat.leb_le.
        exact Hcount.
      }
      rewrite Hdense.
      eexists.
      reflexivity.
  - simpl.
    destruct (dense_window span min_active (x :: prefix ++ suffix))
      eqn:Hdense_now.
    + eexists.
      reflexivity.
    + destruct (IH suffix span min_active Hcount) as [idx Hidx].
      rewrite Hidx.
      eexists.
      reflexivity.
Qed.

Corollary has_dense_window_complete_from_suffix :
  forall prefix suffix span min_active,
    min_active <= window_active_count span suffix ->
    has_dense_window span min_active (prefix ++ suffix) = true.
Proof.
  intros prefix suffix span min_active Hcount.
  destruct (first_dense_window_complete_from_suffix prefix suffix span min_active Hcount)
    as [idx Hidx].
  unfold has_dense_window.
  rewrite Hidx.
  reflexivity.
Qed.

Theorem first_dense_window_complete :
  forall prefix block suffix span min_active,
    span <= length block ->
    min_active <= window_active_count span block ->
    exists idx,
      first_dense_window span min_active (prefix ++ block ++ suffix) = Some idx.
Proof.
  induction prefix as [|x prefix IH]; intros block suffix span min_active Hspan Hdense.
  - destruct (block ++ suffix) as [|w ws] eqn:Htrace.
    + assert (Hnil : block = [] /\ suffix = []).
      { apply app_eq_nil in Htrace.
        exact Htrace. }
      destruct Hnil as [Hblock Hsuffix].
      subst block suffix.
      simpl in Hspan.
      assert (span = 0).
      { lia. }
      subst span.
      unfold window_active_count in Hdense.
      simpl in Hdense.
      assert (min_active = 0).
      { lia. }
      subst min_active.
      simpl.
      eexists.
      reflexivity.
    + simpl.
      assert (Hhead : dense_window span min_active (block ++ suffix) = true).
      {
        unfold dense_window, window_active_count.
        rewrite take_app_prefix with (ys := suffix).
        - apply Nat.leb_le.
          exact Hdense.
        - exact Hspan.
      }
      rewrite <- Htrace.
      rewrite Hhead.
      eexists.
      reflexivity.
  - simpl.
    destruct (dense_window span min_active ((x :: prefix) ++ block ++ suffix))
      eqn:Hdense_now.
    + change (dense_window span min_active (x :: prefix ++ block ++ suffix) = true)
        in Hdense_now.
      rewrite Hdense_now.
      eexists.
      reflexivity.
    + change (dense_window span min_active (x :: prefix ++ block ++ suffix) = false)
        in Hdense_now.
      destruct (IH block suffix span min_active Hspan Hdense) as [idx Hidx].
      rewrite Hdense_now.
      rewrite Hidx.
      eexists.
      reflexivity.
Qed.

Corollary has_dense_window_complete :
  forall prefix block suffix span min_active,
    span <= length block ->
    min_active <= window_active_count span block ->
    has_dense_window span min_active (prefix ++ block ++ suffix) = true.
Proof.
  intros prefix block suffix span min_active Hspan Hdense.
  destruct (first_dense_window_complete prefix block suffix span min_active Hspan Hdense)
    as [idx Hidx].
  unfold has_dense_window.
  rewrite Hidx.
  reflexivity.
Qed.

Lemma first_true_sound_match :
  forall xs,
    match first_true xs with
    | Some idx =>
        idx < length xs /\
        nth idx xs false = true /\
        (forall j, j < idx -> nth j xs false = false)
    | None => True
    end.
Proof.
  induction xs as [|x xs IH]; simpl.
  - trivial.
  - destruct x.
    + split.
      * simpl.
        lia.
      * split.
        -- reflexivity.
        -- intros j Hj.
           assert (False) by lia.
           contradiction.
    + destruct (first_true xs) as [idx|] eqn:Hfirst; simpl.
      * destruct IH as [Hlt [Hnth Hprefix]].
        repeat split.
        -- simpl.
           lia.
        -- simpl.
           exact Hnth.
        -- intros j Hj.
           destruct j.
           ++ reflexivity.
           ++ simpl.
              apply Hprefix.
              lia.
      * trivial.
Qed.

Theorem first_true_sound :
  forall xs idx,
    first_true xs = Some idx ->
    idx < length xs /\
    nth idx xs false = true /\
    (forall j, j < idx -> nth j xs false = false).
Proof.
  intros xs idx H.
  pose proof (first_true_sound_match xs) as Hsound.
  rewrite H in Hsound.
  exact Hsound.
Qed.

Theorem last_true_none_all_false :
  forall xs,
    last_true xs = None ->
    forall j, j < length xs -> nth j xs false = false.
Proof.
  induction xs as [|x xs IH]; intros Hnone j Hj.
  - destruct j; reflexivity.
  - simpl in Hnone.
    destruct (last_true xs) eqn:Hlast.
    + discriminate.
    + destruct x.
      * discriminate.
      * destruct j.
        -- reflexivity.
        -- simpl.
           simpl in Hj.
           assert (Hj' : j < length xs).
           { lia. }
           apply IH.
           ++ exact Hnone.
           ++ exact Hj'.
Qed.

Lemma last_true_sound_match :
  forall xs,
    match last_true xs with
    | Some idx =>
        idx < length xs /\
        nth idx xs false = true /\
        (forall j, idx < j -> j < length xs -> nth j xs false = false)
    | None => True
    end.
Proof.
  induction xs as [|x xs IH]; simpl.
  - trivial.
  - destruct (last_true xs) eqn:Hlast; simpl.
    + destruct IH as [Hlt [Hnth Hsuffix]].
      repeat split.
      * simpl.
        lia.
      * simpl.
        exact Hnth.
      * intros j Hij Hjlen.
        destruct j.
        -- lia.
        -- simpl.
           apply Hsuffix.
           ++ lia.
           ++ lia.
    + destruct x.
      * split.
        -- simpl.
           lia.
        -- split.
           ++ reflexivity.
           ++ intros j Hij Hjlen.
              destruct j.
              ** lia.
              ** simpl.
                 simpl in Hjlen.
                 assert (Hjlen' : j < length xs).
                 { lia. }
                 eapply last_true_none_all_false.
                 --- exact Hlast.
                 --- exact Hjlen'.
      * trivial.
Qed.

Theorem last_true_sound :
  forall xs idx,
    last_true xs = Some idx ->
    idx < length xs /\
    nth idx xs false = true /\
    (forall j, idx < j -> j < length xs -> nth j xs false = false).
Proof.
  intros xs idx H.
  pose proof (last_true_sound_match xs) as Hsound.
  rewrite H in Hsound.
  exact Hsound.
Qed.

Definition Run := (Window * nat)%type.
Definition Runs := list Run.

Fixpoint repeat_window (b : Window) (n : nat) : Trace :=
  match n with
  | O => []
  | S n' => b :: repeat_window b n'
  end.

Lemma repeat_window_snoc :
  forall b n,
    repeat_window b n ++ [b] = repeat_window b (S n).
Proof.
  intros b n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_shift :
  forall b n xs,
    b :: repeat_window b n ++ xs = repeat_window b n ++ b :: xs.
Proof.
  intros b n xs.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_length :
  forall b n,
    length (repeat_window b n) = n.
Proof.
  intros b n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma repeat_window_app :
  forall b n m,
    repeat_window b (n + m) = repeat_window b n ++ repeat_window b m.
Proof.
  intros b n m.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Fixpoint flatten_runs (rs : Runs) : Trace :=
  match rs with
  | [] => []
  | (b, n) :: rs' => repeat_window b n ++ flatten_runs rs'
  end.

Fixpoint runs_of_trace (current : Window) (len : nat) (xs : Trace) : Runs :=
  match xs with
  | [] => [(current, len)]
  | x :: xs' =>
      if Bool.eqb x current then
        runs_of_trace current (S len) xs'
      else
        (current, len) :: runs_of_trace x 1 xs'
  end.

Definition rle_trace (xs : Trace) : Runs :=
  match xs with
  | [] => []
  | x :: xs' => runs_of_trace x 1 xs'
  end.

Fixpoint runs_positive (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (_, O) :: _ => false
  | (_, S _) :: rs' => runs_positive rs'
  end.

Fixpoint runs_alternate_from (current : Window) (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (b, _) :: rs' =>
      negb (Bool.eqb b current) && runs_alternate_from b rs'
  end.

Definition runs_alternating (rs : Runs) : bool :=
  match rs with
  | [] => true
  | (b, _) :: rs' => runs_alternate_from b rs'
  end.

Fixpoint active_run_lengths (rs : Runs) : list nat :=
  match rs with
  | [] => []
  | (b, n) :: rs' =>
      if b then n :: active_run_lengths rs' else active_run_lengths rs'
  end.

Fixpoint inactive_run_lengths (rs : Runs) : list nat :=
  match rs with
  | [] => []
  | (b, n) :: rs' =>
      if b then inactive_run_lengths rs' else n :: inactive_run_lengths rs'
  end.

Fixpoint strip_leading_false_runs (rs : Runs) : Runs :=
  match rs with
  | (false, _) :: rs' => strip_leading_false_runs rs'
  | _ => rs
  end.

Definition strip_trailing_false_runs (rs : Runs) : Runs :=
  rev (strip_leading_false_runs (rev rs)).

Definition canonical_runs (rs : Runs) : Runs :=
  strip_trailing_false_runs (strip_leading_false_runs rs).

Lemma active_run_lengths_strip_leading_false_runs :
  forall rs,
    active_run_lengths (strip_leading_false_runs rs) = active_run_lengths rs.
Proof.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + exact IH.
Qed.

Lemma active_run_lengths_app :
  forall rs1 rs2,
    active_run_lengths (rs1 ++ rs2) =
      active_run_lengths rs1 ++ active_run_lengths rs2.
Proof.
  induction rs1 as [|(b, n) rs1 IH]; intros rs2; simpl.
  - reflexivity.
  - destruct b; simpl.
    + rewrite (IH rs2).
      reflexivity.
    + exact (IH rs2).
Qed.

Lemma active_run_lengths_rev :
  forall rs,
    active_run_lengths (rev rs) = rev (active_run_lengths rs).
Proof.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - rewrite active_run_lengths_app.
    rewrite IH.
    destruct b; simpl.
    + reflexivity.
    + rewrite app_nil_r.
      reflexivity.
Qed.

Lemma active_run_lengths_strip_trailing_false_runs :
  forall rs,
    active_run_lengths (strip_trailing_false_runs rs) = active_run_lengths rs.
Proof.
  intro rs.
  unfold strip_trailing_false_runs.
  rewrite active_run_lengths_rev.
  rewrite active_run_lengths_strip_leading_false_runs.
  rewrite active_run_lengths_rev.
  rewrite rev_involutive.
  reflexivity.
Qed.

Corollary active_run_lengths_canonical_runs :
  forall rs,
    active_run_lengths (canonical_runs rs) = active_run_lengths rs.
Proof.
  intros rs.
  unfold canonical_runs.
  rewrite active_run_lengths_strip_trailing_false_runs.
  apply active_run_lengths_strip_leading_false_runs.
Qed.

Definition scale_run (factor : nat) (r : Run) : Run :=
  let '(b, n) := r in
  (b, factor * n).

Definition scale_runs (factor : nat) (rs : Runs) : Runs :=
  map (scale_run factor) rs.

Lemma scale_runs_length :
  forall factor rs,
    length (scale_runs factor rs) = length rs.
Proof.
  intros factor rs.
  unfold scale_runs.
  rewrite length_map.
  reflexivity.
Qed.

Lemma scale_runs_app :
  forall factor rs1 rs2,
    scale_runs factor (rs1 ++ rs2) =
      scale_runs factor rs1 ++ scale_runs factor rs2.
Proof.
  intros factor rs1 rs2.
  unfold scale_runs.
  rewrite map_app.
  reflexivity.
Qed.

Lemma scale_runs_rev :
  forall factor rs,
    scale_runs factor (rev rs) = rev (scale_runs factor rs).
Proof.
  intros factor rs.
  unfold scale_runs.
  rewrite map_rev.
  reflexivity.
Qed.

Lemma active_run_lengths_scale :
  forall factor rs,
    active_run_lengths (scale_runs factor rs) =
      map (Nat.mul factor) (active_run_lengths rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + rewrite IH.
      reflexivity.
    + exact IH.
Qed.

Lemma inactive_run_lengths_scale :
  forall factor rs,
    inactive_run_lengths (scale_runs factor rs) =
      map (Nat.mul factor) (inactive_run_lengths rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + exact IH.
    + rewrite IH.
      reflexivity.
Qed.

Theorem runs_positive_scale :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_positive (scale_runs factor rs) = true.
Proof.
  intros factor rs Hfactor Hpos.
  destruct factor as [|factor'].
  { lia. }
  induction rs as [|(b, n) rs IH]; simpl in *.
  - reflexivity.
  - destruct n.
    + discriminate.
    + destruct b; simpl.
      * apply IH.
        exact Hpos.
      * apply IH.
        exact Hpos.
Qed.

Theorem runs_alternating_scale :
  forall factor rs,
    runs_alternating rs = true ->
    runs_alternating (scale_runs factor rs) = true.
Proof.
  intros factor rs.
  unfold runs_alternating.
  destruct rs as [|(b, n) rs']; simpl.
  - reflexivity.
  - revert b.
    induction rs' as [|(b', n') rs'' IH]; intros b Halt; simpl in *.
    + reflexivity.
    + apply andb_true_iff in Halt as [Hneq Hrest].
      apply andb_true_iff.
      split.
      * exact Hneq.
      * apply IH.
        exact Hrest.
Qed.

Lemma flatten_runs_of_trace :
  forall current len xs,
    0 < len ->
    flatten_runs (runs_of_trace current len xs) = repeat_window current len ++ xs.
Proof.
  intros current len xs.
  revert current len.
  induction xs as [|x xs IH]; intros current len Hlen.
  - simpl.
    reflexivity.
  - simpl.
    destruct (Bool.eqb x current) eqn:Heq.
    + destruct x, current; simpl in Heq; try discriminate.
      * rewrite IH.
        -- simpl.
           apply repeat_window_shift.
        -- lia.
      * rewrite IH.
        -- simpl.
           apply repeat_window_shift.
        -- lia.
    + simpl.
      rewrite IH.
      * simpl.
        reflexivity.
      * lia.
Qed.

Lemma runs_of_trace_extend_same :
  forall current len extra xs,
    runs_of_trace current len (repeat_window current extra ++ xs) =
      runs_of_trace current (len + extra) xs.
Proof.
  intros current len extra xs.
  revert current len xs.
  induction extra as [|extra IH]; intros current len xs; simpl.
  - replace (len + 0) with len by lia.
    reflexivity.
  - simpl.
    simpl.
    rewrite (IH current (S len) xs).
    destruct (Bool.eqb current current) eqn:Heq.
    + replace (S len + extra) with (len + S extra) by lia.
      reflexivity.
    + apply Bool.eqb_false_iff in Heq.
      contradiction Heq.
      reflexivity.
Qed.

Theorem flatten_rle_trace :
  forall xs,
    flatten_runs (rle_trace xs) = xs.
Proof.
  intros xs.
  destruct xs as [|x xs'].
  - reflexivity.
  - unfold rle_trace.
    rewrite flatten_runs_of_trace.
    + simpl.
      reflexivity.
    + lia.
Qed.

Lemma runs_of_trace_flatten_runs :
  forall current len rs,
    0 < len ->
    runs_positive rs = true ->
    runs_alternate_from current rs = true ->
    runs_of_trace current len (flatten_runs rs) = (current, len) :: rs.
Proof.
  intros current len rs Hlen.
  revert current len Hlen.
  induction rs as [|(b, n) rs' IH]; intros current len Hlen Hpos Halt; simpl in *.
  - reflexivity.
  - destruct n as [|n']; [discriminate|].
    apply andb_true_iff in Halt as [Hneq Hrest].
    apply Bool.negb_true_iff in Hneq.
    apply Bool.eqb_false_iff in Hneq.
    simpl.
    assert (Hneqb : Bool.eqb b current = false).
    { apply Bool.eqb_false_iff.
      exact Hneq. }
    rewrite Hneqb.
    rewrite runs_of_trace_extend_same.
    f_equal.
    apply IH.
    * lia.
    * exact Hpos.
    * exact Hrest.
Qed.

Theorem rle_trace_flatten_runs_well_formed :
  forall rs,
    runs_positive rs = true ->
    runs_alternating rs = true ->
    rle_trace (flatten_runs rs) = rs.
Proof.
  intros rs Hpos Halt.
  destruct rs as [|(b, n) rs']; simpl in *.
  - reflexivity.
  - destruct n as [|n']; [discriminate|].
    simpl.
    rewrite runs_of_trace_extend_same.
    apply runs_of_trace_flatten_runs.
    + lia.
    + exact Hpos.
    + exact Halt.
Qed.

Lemma runs_of_trace_positive :
  forall current len xs,
    0 < len ->
    runs_positive (runs_of_trace current len xs) = true.
Proof.
  intros current len xs.
  revert current len.
  induction xs as [|x xs IH]; intros current len Hlen.
  - simpl.
    destruct len; [lia|reflexivity].
  - simpl.
    destruct (Bool.eqb x current) eqn:Heq.
    + apply IH.
      lia.
    + simpl.
      destruct len; [lia|].
      simpl.
      apply IH.
      lia.
Qed.

Theorem rle_trace_positive :
  forall xs,
    runs_positive (rle_trace xs) = true.
Proof.
  intros xs.
  destruct xs as [|x xs'].
  - reflexivity.
  - unfold rle_trace.
    apply runs_of_trace_positive.
    lia.
Qed.

Fixpoint min_list_from (current : nat) (xs : list nat) : nat :=
  match xs with
  | [] => current
  | x :: xs' => min_list_from (Nat.min current x) xs'
  end.

Definition min_list_default (default : nat) (xs : list nat) : nat :=
  match xs with
  | [] => default
  | x :: xs' => min_list_from x xs'
  end.

Inductive PulseClass :=
| MarkShort
| MarkLong
| GapShort
| GapLong
| GapBreak.

Inductive CoarsePulseClass :=
| CoarseMarkShort
| CoarseMarkLong
| CoarseGap
| CoarseGapBreak.

Definition classify_run_with_base (base : nat) (r : Run) : PulseClass :=
  let '(b, n) := r in
  if b then
    if Nat.ltb n (2 * base) then MarkShort else MarkLong
  else
    if Nat.ltb n (2 * base) then GapShort
    else if Nat.ltb n (10 * base) then GapLong
    else GapBreak.

Definition classify_runs_with_base (base : nat) (rs : Runs) : list PulseClass :=
  map (classify_run_with_base base) rs.

Definition coarsen_pulse_class (cls : PulseClass) : CoarsePulseClass :=
  match cls with
  | MarkShort => CoarseMarkShort
  | MarkLong => CoarseMarkLong
  | GapShort => CoarseGap
  | GapLong => CoarseGap
  | GapBreak => CoarseGapBreak
  end.

Definition coarse_pulse_classes (xs : list PulseClass) : list CoarsePulseClass :=
  map coarsen_pulse_class xs.

Definition pulse_base_from_runs (rs : Runs) : nat :=
  min_list_default 1 (active_run_lengths rs).

Definition normalized_pulse_classes (rs : Runs) : list PulseClass :=
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Definition canonical_pulse_base_from_runs (rs : Runs) : nat :=
  pulse_base_from_runs (canonical_runs rs).

Definition canonical_normalized_pulse_classes (rs : Runs) : list PulseClass :=
  normalized_pulse_classes (canonical_runs rs).

Inductive FrameToken :=
| FrameBitZero
| FrameBitOne
| FrameBreak
| FrameUnknown.

Fixpoint frame_tokens_from_classes (xs : list PulseClass) : list FrameToken :=
  match xs with
  | [] => []
  | GapBreak :: xs' => FrameBreak :: frame_tokens_from_classes xs'
  | MarkShort :: GapLong :: xs' =>
      FrameBitZero :: frame_tokens_from_classes xs'
  | MarkLong :: GapShort :: xs' =>
      FrameBitOne :: frame_tokens_from_classes xs'
  | _ :: xs' => FrameUnknown :: frame_tokens_from_classes xs'
  end.

Fixpoint first_frame_bits_from_tokens_aux
    (started : bool)
    (xs : list FrameToken)
    : list bool :=
  match xs with
  | [] => []
  | FrameBreak :: xs' =>
      if started then [] else first_frame_bits_from_tokens_aux false xs'
  | FrameBitZero :: xs' =>
      false :: first_frame_bits_from_tokens_aux true xs'
  | FrameBitOne :: xs' =>
      true :: first_frame_bits_from_tokens_aux true xs'
  | FrameUnknown :: xs' =>
      if started then [] else first_frame_bits_from_tokens_aux false xs'
  end.

Definition first_frame_bits_from_tokens (xs : list FrameToken) : list bool :=
  first_frame_bits_from_tokens_aux false xs.

Definition token_noise_prefix (xs : list FrameToken) : Prop :=
  Forall (fun tok => tok = FrameBreak \/ tok = FrameUnknown) xs.

Lemma first_frame_bits_from_tokens_aux_true_app_break :
  forall xs ys,
    first_frame_bits_from_tokens_aux true (xs ++ FrameBreak :: ys) =
      first_frame_bits_from_tokens_aux true xs.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - reflexivity.
  - destruct x; simpl.
    + rewrite IH.
      reflexivity.
    + rewrite IH.
      reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Theorem first_frame_bits_from_tokens_prefix_noise_invariant :
  forall prefix xs,
    token_noise_prefix prefix ->
    first_frame_bits_from_tokens (prefix ++ xs) =
      first_frame_bits_from_tokens xs.
Proof.
  intros prefix xs Hnoise.
  induction Hnoise; simpl.
  - reflexivity.
  - destruct H as [Hbreak | Hunknown]; subst; simpl; exact IHHnoise.
Qed.

Theorem first_frame_bits_from_tokens_suffix_break_invariant :
  forall xs,
    first_frame_bits_from_tokens (xs ++ [FrameBreak]) =
      first_frame_bits_from_tokens xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - unfold first_frame_bits_from_tokens in *.
    simpl.
    destruct x; simpl.
    + f_equal.
      apply first_frame_bits_from_tokens_aux_true_app_break.
    + f_equal.
      apply first_frame_bits_from_tokens_aux_true_app_break.
    + exact IH.
    + exact IH.
Qed.

Definition frame_bits_from_classes (xs : list PulseClass) : list bool :=
  first_frame_bits_from_tokens (frame_tokens_from_classes xs).

Fixpoint classes_of_bits (xs : list bool) : list PulseClass :=
  match xs with
  | [] => [GapBreak]
  | false :: xs' => MarkShort :: GapLong :: classes_of_bits xs'
  | true :: xs' => MarkLong :: GapShort :: classes_of_bits xs'
  end.

Lemma frame_tokens_from_classes_of_bits :
  forall xs,
    frame_tokens_from_classes (classes_of_bits xs) =
      map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak].
Proof.
  induction xs as [|b xs IH]; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma frame_tokens_from_classes_of_bits_app :
  forall xs suffix,
    frame_tokens_from_classes (classes_of_bits xs ++ suffix) =
      map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++
      frame_tokens_from_classes (GapBreak :: suffix).
Proof.
  induction xs as [|b xs IH]; intro suffix; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma first_frame_bits_from_bit_tokens_aux_true :
  forall xs,
    first_frame_bits_from_tokens_aux true
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak]) = xs.
Proof.
  induction xs as [|b xs IH]; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma first_frame_bits_from_bit_tokens :
  forall xs,
    first_frame_bits_from_tokens
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ [FrameBreak]) = xs.
Proof.
  intro xs.
  unfold first_frame_bits_from_tokens.
  simpl.
  destruct xs as [|b xs].
  - reflexivity.
  - destruct b; simpl; f_equal; apply first_frame_bits_from_bit_tokens_aux_true.
Qed.

Lemma first_frame_bits_from_bit_tokens_then_break_suffix :
  forall xs ys,
    first_frame_bits_from_tokens_aux true
      (map (fun b : bool => if b then FrameBitOne else FrameBitZero) xs ++ FrameBreak :: ys) = xs.
Proof.
  induction xs as [|b xs IH]; intro ys; simpl.
  - reflexivity.
  - destruct b; simpl; f_equal; apply IH.
Qed.

Theorem frame_bits_from_classes_of_bits :
  forall xs,
    frame_bits_from_classes (classes_of_bits xs) = xs.
Proof.
  intro xs.
  unfold frame_bits_from_classes.
  rewrite frame_tokens_from_classes_of_bits.
  apply first_frame_bits_from_bit_tokens.
Qed.

Theorem frame_bits_from_classes_of_bits_with_suffix :
  forall xs suffix,
    xs <> [] ->
    frame_bits_from_classes (classes_of_bits xs ++ suffix) = xs.
Proof.
  intros xs suffix Hnonempty.
  destruct xs as [|b xs].
  - contradiction.
  - unfold frame_bits_from_classes.
    rewrite frame_tokens_from_classes_of_bits_app.
    unfold first_frame_bits_from_tokens.
    simpl.
    destruct b; simpl; f_equal;
      apply first_frame_bits_from_bit_tokens_then_break_suffix.
Qed.

Definition packet_alias_classes (xs ys : list PulseClass) : Prop :=
  frame_bits_from_classes xs = frame_bits_from_classes ys.

Theorem classes_of_bits_suffix_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet_alias_classes
      (classes_of_bits bits ++ suffix1)
      (classes_of_bits bits ++ suffix2).
Proof.
  intros bits suffix1 suffix2 Hbits.
  unfold packet_alias_classes.
  rewrite (frame_bits_from_classes_of_bits_with_suffix bits suffix1 Hbits).
  rewrite (frame_bits_from_classes_of_bits_with_suffix bits suffix2 Hbits).
  reflexivity.
Qed.

Theorem packet_alias_classes_noninjective :
  forall bits,
    bits <> [] ->
    exists xs ys,
      xs <> ys /\
      frame_bits_from_classes xs = bits /\
      frame_bits_from_classes ys = bits.
Proof.
  intros bits Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - split.
    + apply frame_bits_from_classes_of_bits_with_suffix.
      exact Hbits.
    + apply frame_bits_from_classes_of_bits_with_suffix.
      exact Hbits.
Qed.

Theorem packet_alias_classes_infinite_tail_family :
  forall bits n1 n2,
    bits <> [] ->
    packet_alias_classes
      (classes_of_bits bits ++ repeat MarkShort n1)
      (classes_of_bits bits ++ repeat MarkShort n2).
Proof.
  intros bits n1 n2 Hbits.
  apply classes_of_bits_suffix_alias.
  exact Hbits.
Qed.

Theorem packet_alias_classes_tail_family_distinct :
  forall bits n1 n2,
    bits <> [] ->
    n1 <> n2 ->
    classes_of_bits bits ++ repeat MarkShort n1 <>
      classes_of_bits bits ++ repeat MarkShort n2.
Proof.
  intros bits n1 n2 Hbits Hneq Heq.
  assert (Hlen :
    length (classes_of_bits bits ++ repeat MarkShort n1) =
    length (classes_of_bits bits ++ repeat MarkShort n2)).
  { rewrite Heq. reflexivity. }
  repeat rewrite length_app in Hlen.
  repeat rewrite repeat_length in Hlen.
  lia.
Qed.

Corollary frame_bits_from_classes_token_suffix_break_invariant :
  forall xs,
    first_frame_bits_from_tokens (frame_tokens_from_classes xs ++ [FrameBreak]) =
      frame_bits_from_classes xs.
Proof.
  intro xs.
  unfold frame_bits_from_classes.
  apply first_frame_bits_from_tokens_suffix_break_invariant.
Qed.

Definition canonical_frame_bits_from_runs (rs : Runs) : list bool :=
  frame_bits_from_classes (canonical_normalized_pulse_classes rs).

Fixpoint bits_to_nat_acc (acc : nat) (xs : list bool) : nat :=
  match xs with
  | [] => acc
  | x :: xs' =>
      bits_to_nat_acc (2 * acc + if x then 1 else 0) xs'
  end.

Definition bits_to_nat (xs : list bool) : nat :=
  bits_to_nat_acc 0 xs.

Definition canonical_frame_word_from_runs (rs : Runs) : nat :=
  bits_to_nat (canonical_frame_bits_from_runs rs).

Record Packet24 := {
  packet24_hi : nat;
  packet24_mid : nat;
  packet24_lo : nat
}.

Definition packet24_from_bits (xs : list bool) : Packet24 :=
  {| packet24_hi := bits_to_nat (take 8 xs);
     packet24_mid := bits_to_nat (take 8 (drop 8 xs));
     packet24_lo := bits_to_nat (take 8 (drop 16 xs)) |}.

Definition canonical_packet24_from_runs (rs : Runs) : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_runs rs).

Record DecodedPacketView := {
  view_bits : list bool;
  view_word : nat;
  view_packet24 : Packet24
}.

Definition decoded_packet_view_from_classes
    (xs : list PulseClass)
    : DecodedPacketView :=
  {| view_bits := frame_bits_from_classes xs;
     view_word := bits_to_nat (frame_bits_from_classes xs);
     view_packet24 := packet24_from_bits (frame_bits_from_classes xs) |}.

Definition decoded_packet_view_from_runs
    (rs : Runs)
    : DecodedPacketView :=
  decoded_packet_view_from_classes (canonical_normalized_pulse_classes rs).

Theorem classes_of_bits_suffix_word_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    bits_to_nat (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      bits_to_nat (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_packet24_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    packet24_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix1)) =
      packet24_from_bits (frame_bits_from_classes (classes_of_bits bits ++ suffix2)).
Proof.
  intros bits suffix1 suffix2 Hbits.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem classes_of_bits_suffix_view_alias :
  forall bits suffix1 suffix2,
    bits <> [] ->
    decoded_packet_view_from_classes (classes_of_bits bits ++ suffix1) =
      decoded_packet_view_from_classes (classes_of_bits bits ++ suffix2).
Proof.
  intros bits suffix1 suffix2 Hbits.
  unfold decoded_packet_view_from_classes.
  rewrite (classes_of_bits_suffix_alias bits suffix1 suffix2 Hbits).
  reflexivity.
Qed.

Theorem decoded_packet_view_noninjective :
  forall bits,
    bits <> ([] : list bool) ->
    exists xs ys,
      xs <> ys /\
      decoded_packet_view_from_classes xs = decoded_packet_view_from_classes ys.
Proof.
  intros bits Hbits.
  exists (classes_of_bits bits ++ [MarkShort]).
  exists (classes_of_bits bits ++ [MarkShort; MarkShort]).
  split.
  - intro Heq.
    assert (Hlen :
      length (classes_of_bits bits ++ [MarkShort]) =
      length (classes_of_bits bits ++ [MarkShort; MarkShort])).
    { rewrite Heq. reflexivity. }
    repeat rewrite length_app in Hlen.
    simpl in Hlen.
    lia.
  - apply classes_of_bits_suffix_view_alias.
    exact Hbits.
Qed.

Theorem decoded_packet_view_infinite_tail_family :
  forall bits n1 n2,
    bits <> ([] : list bool) ->
    decoded_packet_view_from_classes
      (classes_of_bits bits ++ repeat MarkShort n1) =
    decoded_packet_view_from_classes
      (classes_of_bits bits ++ repeat MarkShort n2).
Proof.
  intros bits n1 n2 Hbits.
  apply classes_of_bits_suffix_view_alias.
  exact Hbits.
Qed.

Theorem decoded_packet_view_tail_family_distinct :
  forall bits n1 n2,
    bits <> ([] : list bool) ->
    n1 <> n2 ->
    classes_of_bits bits ++ repeat MarkShort n1 <>
      classes_of_bits bits ++ repeat MarkShort n2.
Proof.
  intros bits n1 n2 Hbits Hneq.
  apply packet_alias_classes_tail_family_distinct.
  - exact Hbits.
  - exact Hneq.
Qed.

Theorem pulse_base_from_runs_canonical :
  forall rs,
    canonical_pulse_base_from_runs rs = pulse_base_from_runs rs.
Proof.
  intro rs.
  unfold canonical_pulse_base_from_runs, pulse_base_from_runs.
  rewrite active_run_lengths_canonical_runs.
  reflexivity.
Qed.

Theorem canonical_runs_prefix_false_invariant :
  forall n rs,
    canonical_runs ((false, n) :: rs) = canonical_runs rs.
Proof.
  intros n rs.
  unfold canonical_runs.
  reflexivity.
Qed.

Lemma strip_trailing_false_runs_app_false :
  forall rs n,
    strip_trailing_false_runs (rs ++ [(false, n)]) = strip_trailing_false_runs rs.
Proof.
  intros rs n.
  unfold strip_trailing_false_runs.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma strip_leading_false_runs_app_false :
  forall rs n,
    strip_leading_false_runs (rs ++ [(false, n)]) =
      match strip_leading_false_runs rs with
      | [] => []
      | rs' => rs' ++ [(false, n)]
      end.
Proof.
  induction rs as [|(b, m) rs IH]; intro n; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + exact (IH n).
Qed.

Theorem canonical_runs_suffix_false_invariant :
  forall n rs,
    canonical_runs (rs ++ [(false, n)]) = canonical_runs rs.
Proof.
  intros n rs.
  unfold canonical_runs.
  rewrite strip_leading_false_runs_app_false.
  destruct (strip_leading_false_runs rs) as [|r rs'] eqn:Hlead.
  - reflexivity.
  - simpl.
    replace (r :: rs' ++ [(false, n)]) with ((r :: rs') ++ [(false, n)]) by reflexivity.
    apply strip_trailing_false_runs_app_false.
Qed.

Theorem strip_leading_false_runs_scale_commute :
  forall factor rs,
    strip_leading_false_runs (scale_runs factor rs) =
      scale_runs factor (strip_leading_false_runs rs).
Proof.
  intros factor rs.
  induction rs as [|(b, n) rs IH]; simpl.
  - reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Theorem strip_trailing_false_runs_scale_commute :
  forall factor rs,
    strip_trailing_false_runs (scale_runs factor rs) =
      scale_runs factor (strip_trailing_false_runs rs).
Proof.
  intros factor rs.
  unfold strip_trailing_false_runs.
  rewrite <- scale_runs_rev.
  rewrite strip_leading_false_runs_scale_commute.
  rewrite scale_runs_rev.
  reflexivity.
Qed.

Theorem canonical_runs_scale_commute :
  forall factor rs,
    canonical_runs (scale_runs factor rs) =
      scale_runs factor (canonical_runs rs).
Proof.
  intros factor rs.
  unfold canonical_runs.
  rewrite strip_leading_false_runs_scale_commute.
  rewrite strip_trailing_false_runs_scale_commute.
  reflexivity.
Qed.

Lemma min_list_from_scale :
  forall factor current xs,
    min_list_from (factor * current) (map (Nat.mul factor) xs) =
      factor * min_list_from current xs.
Proof.
  intros factor current xs.
  revert current.
  induction xs as [|x xs IH]; intros current; simpl.
  - reflexivity.
  - rewrite Nat.mul_min_distr_l.
    rewrite IH.
    reflexivity.
Qed.

Lemma min_list_default_scale_nonempty :
  forall factor xs,
    xs <> [] ->
    min_list_default 1 (map (Nat.mul factor) xs) =
      factor * min_list_default 1 xs.
Proof.
  intros factor xs Hnonempty.
  destruct xs as [|x xs'].
  - contradiction.
  - simpl.
    apply min_list_from_scale.
Qed.

Theorem pulse_base_from_runs_scale :
  forall factor rs,
    active_run_lengths rs <> [] ->
    pulse_base_from_runs (scale_runs factor rs) =
      factor * pulse_base_from_runs rs.
Proof.
  intros factor rs Hactive.
  unfold pulse_base_from_runs.
  rewrite active_run_lengths_scale.
  apply min_list_default_scale_nonempty.
  exact Hactive.
Qed.

Lemma ltb_scale_left :
  forall factor n m,
    0 < factor ->
    Nat.ltb (factor * n) (factor * m) = Nat.ltb n m.
Proof.
  intros factor n m Hfactor.
  destruct (Nat.ltb n m) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_lt.
    apply (proj1 (Nat.mul_lt_mono_pos_l factor n m Hfactor)).
    exact Hlt.
  - apply Nat.ltb_ge in Hlt.
    apply Nat.ltb_ge.
    apply Nat.mul_le_mono_l.
    exact Hlt.
Qed.

Lemma scale_two_base :
  forall factor base,
    2 * (factor * base) = factor * (2 * base).
Proof.
  intros factor base.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm 2 factor).
  rewrite <- Nat.mul_assoc.
  reflexivity.
Qed.

Lemma scale_ten_base :
  forall factor base,
    10 * (factor * base) = factor * (10 * base).
Proof.
  intros factor base.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm 10 factor).
  rewrite <- Nat.mul_assoc.
  reflexivity.
Qed.

Theorem classify_run_with_base_scale_invariant :
  forall factor base r,
    0 < factor ->
    classify_run_with_base (factor * base) (scale_run factor r) =
      classify_run_with_base base r.
Proof.
  intros factor base [b n] Hfactor.
  destruct b; cbn [classify_run_with_base scale_run].
  - rewrite scale_two_base.
    rewrite ltb_scale_left by exact Hfactor.
    reflexivity.
  - rewrite scale_two_base.
    rewrite ltb_scale_left by exact Hfactor.
    destruct (Nat.ltb n (2 * base)) eqn:Hshort.
    + reflexivity.
    + rewrite scale_ten_base.
      rewrite ltb_scale_left by exact Hfactor.
      reflexivity.
Qed.

Theorem classify_runs_with_base_scale_invariant :
  forall factor base rs,
    0 < factor ->
    classify_runs_with_base (factor * base) (scale_runs factor rs) =
      classify_runs_with_base base rs.
Proof.
  intros factor base rs Hfactor.
  induction rs as [|r rs IH]; simpl.
  - reflexivity.
  - rewrite classify_run_with_base_scale_invariant by exact Hfactor.
    rewrite IH.
    reflexivity.
Qed.

Theorem pulse_classes_from_scaled_runs_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    classify_runs_with_base
      (pulse_base_from_runs (scale_runs factor rs))
      (scale_runs factor rs) =
    classify_runs_with_base (pulse_base_from_runs rs) rs.
Proof.
  intros factor rs Hfactor Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  apply classify_runs_with_base_scale_invariant.
  exact Hfactor.
Qed.

Corollary pulse_classes_from_doubled_runs_invariant :
  forall rs,
    active_run_lengths rs <> [] ->
    classify_runs_with_base
      (pulse_base_from_runs (scale_runs 2 rs))
      (scale_runs 2 rs) =
    classify_runs_with_base (pulse_base_from_runs rs) rs.
Proof.
  intros rs Hactive.
  apply pulse_classes_from_scaled_runs_invariant.
  - lia.
  - exact Hactive.
Qed.

Theorem classify_runs_with_base_length :
  forall base rs,
    length (classify_runs_with_base base rs) = length rs.
Proof.
  intros base rs.
  unfold classify_runs_with_base.
  rewrite length_map.
  reflexivity.
Qed.

Lemma active_run_lengths_positive :
  forall rs,
    runs_positive rs = true ->
    Forall (fun n => 0 < n) (active_run_lengths rs).
Proof.
  induction rs as [|(b, n) rs IH]; intro Hpos.
  - constructor.
  - simpl in Hpos.
    destruct b.
    + destruct n; try discriminate.
      simpl.
      constructor.
      * lia.
      * apply IH.
        exact Hpos.
    + destruct n; try discriminate.
      apply IH.
      exact Hpos.
Qed.

Lemma min_list_from_positive :
  forall current xs,
    0 < current ->
    Forall (fun n => 0 < n) xs ->
    0 < min_list_from current xs.
Proof.
  intros current xs Hcurrent Hpos.
  revert current Hcurrent.
  induction Hpos as [|x xs Hx Hxs IH]; intros current Hcurrent; simpl.
  - exact Hcurrent.
  - assert (Hmin : 0 < Nat.min current x).
    {
      destruct current, x; simpl in *; lia.
    }
    apply IH.
    exact Hmin.
Qed.

Lemma min_list_default_positive :
  forall default xs,
    0 < default ->
    Forall (fun n => 0 < n) xs ->
    0 < min_list_default default xs.
Proof.
  intros default xs Hdefault Hpos.
  destruct xs as [|x xs'].
  - simpl.
    exact Hdefault.
  - simpl.
    inversion Hpos as [|x' xs'' Hx Hxs]; subst.
    apply min_list_from_positive.
    + exact Hx.
    + exact Hxs.
Qed.

Theorem pulse_base_from_runs_positive :
  forall rs,
    runs_positive rs = true ->
    0 < pulse_base_from_runs rs.
Proof.
  intros rs Hpos.
  unfold pulse_base_from_runs.
  apply min_list_default_positive.
  - lia.
  - apply active_run_lengths_positive.
    exact Hpos.
Qed.

Corollary normalized_pulse_classes_length :
  forall rs,
    length (normalized_pulse_classes rs) = length rs.
Proof.
  intros rs.
  unfold normalized_pulse_classes.
  apply classify_runs_with_base_length.
Qed.

Theorem normalized_pulse_classes_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor rs) = normalized_pulse_classes rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold normalized_pulse_classes.
  apply pulse_classes_from_scaled_runs_invariant.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary normalized_pulse_classes_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor1 rs) =
      normalized_pulse_classes (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (normalized_pulse_classes rs).
  - apply normalized_pulse_classes_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply normalized_pulse_classes_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem normalized_pulse_classes_scale_separated :
  forall factor1 factor2 rs1 rs2,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs1 <> [] ->
    active_run_lengths rs2 <> [] ->
    normalized_pulse_classes rs1 <> normalized_pulse_classes rs2 ->
    normalized_pulse_classes (scale_runs factor1 rs1) <>
      normalized_pulse_classes (scale_runs factor2 rs2).
Proof.
  intros factor1 factor2 rs1 rs2 Hfactor1 Hfactor2 Hactive1 Hactive2 Hneq Heq.
  apply Hneq.
  rewrite <- (normalized_pulse_classes_scale_invariant factor1 rs1 Hfactor1 Hactive1).
  rewrite <- (normalized_pulse_classes_scale_invariant factor2 rs2 Hfactor2 Hactive2).
  exact Heq.
Qed.

Corollary normalized_pulse_classes_double_triple_equal :
  forall rs,
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs 2 rs) =
      normalized_pulse_classes (scale_runs 3 rs).
Proof.
  intros rs Hactive.
  apply normalized_pulse_classes_pairwise_scale_equal.
  - lia.
  - lia.
  - exact Hactive.
Qed.

Theorem pulse_base_from_runs_scale_strict_order :
  forall factor1 factor2 rs,
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    pulse_base_from_runs (scale_runs factor1 rs) <
      pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hlt Hpos Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  rewrite pulse_base_from_runs_scale by exact Hactive.
  assert (Hbase : 0 < pulse_base_from_runs rs).
  {
    apply pulse_base_from_runs_positive.
    exact Hpos.
  }
  apply (proj1 (Nat.mul_lt_mono_pos_r (pulse_base_from_runs rs) factor1 factor2 Hbase)).
  exact Hlt.
Qed.

Theorem normalized_pulse_classes_equal_but_bases_ordered :
  forall factor1 factor2 rs,
    0 < factor1 ->
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs factor1 rs) =
      normalized_pulse_classes (scale_runs factor2 rs) /\
    pulse_base_from_runs (scale_runs factor1 rs) <
      pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hlt Hpos Hactive.
  split.
  - apply normalized_pulse_classes_pairwise_scale_equal.
    + exact Hfactor1.
    + lia.
    + exact Hactive.
  - apply pulse_base_from_runs_scale_strict_order.
    + exact Hlt.
    + exact Hpos.
    + exact Hactive.
Qed.

Corollary normalized_pulse_classes_double_triple_same_but_bases_ordered :
  forall rs,
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    normalized_pulse_classes (scale_runs 2 rs) =
      normalized_pulse_classes (scale_runs 3 rs) /\
    pulse_base_from_runs (scale_runs 2 rs) <
      pulse_base_from_runs (scale_runs 3 rs).
Proof.
  intros rs Hpos Hactive.
  apply normalized_pulse_classes_equal_but_bases_ordered.
  - lia.
  - lia.
  - exact Hpos.
  - exact Hactive.
Qed.

Corollary canonical_normalized_pulse_classes_prefix_false_invariant :
  forall n rs,
    canonical_normalized_pulse_classes ((false, n) :: rs) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros n rs.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_prefix_false_invariant.
  reflexivity.
Qed.

Corollary canonical_normalized_pulse_classes_suffix_false_invariant :
  forall n rs,
    canonical_normalized_pulse_classes (rs ++ [(false, n)]) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros n rs.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_suffix_false_invariant.
  reflexivity.
Qed.

Theorem canonical_normalized_pulse_classes_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor rs) =
      canonical_normalized_pulse_classes rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_normalized_pulse_classes.
  rewrite canonical_runs_scale_commute.
  apply normalized_pulse_classes_scale_invariant.
  - exact Hfactor.
  - rewrite active_run_lengths_canonical_runs.
    exact Hactive.
Qed.

Theorem canonical_frame_bits_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_frame_bits_from_runs (scale_runs factor rs) =
      canonical_frame_bits_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_frame_bits_from_runs, frame_bits_from_classes.
  rewrite canonical_normalized_pulse_classes_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary canonical_frame_bits_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_frame_bits_from_runs (scale_runs factor1 rs) =
      canonical_frame_bits_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_frame_bits_from_runs rs).
  - apply canonical_frame_bits_from_runs_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_frame_bits_from_runs_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem canonical_frame_word_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_frame_word_from_runs (scale_runs factor rs) =
      canonical_frame_word_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_frame_word_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Theorem canonical_packet24_from_runs_scale_invariant :
  forall factor rs,
    0 < factor ->
    active_run_lengths rs <> [] ->
    canonical_packet24_from_runs (scale_runs factor rs) =
      canonical_packet24_from_runs rs.
Proof.
  intros factor rs Hfactor Hactive.
  unfold canonical_packet24_from_runs.
  rewrite canonical_frame_bits_from_runs_scale_invariant.
  - reflexivity.
  - exact Hfactor.
  - exact Hactive.
Qed.

Corollary canonical_packet24_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_packet24_from_runs (scale_runs factor1 rs) =
      canonical_packet24_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_packet24_from_runs rs).
  - apply canonical_packet24_from_runs_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_packet24_from_runs_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.


Corollary canonical_normalized_pulse_classes_pairwise_scale_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs) =
      canonical_normalized_pulse_classes (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hactive.
  transitivity (canonical_normalized_pulse_classes rs).
  - apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor1.
    + exact Hactive.
  - symmetry.
    apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor2.
    + exact Hactive.
Qed.

Theorem canonical_normalized_pulse_classes_scale_separated :
  forall factor1 factor2 rs1 rs2,
    0 < factor1 ->
    0 < factor2 ->
    active_run_lengths rs1 <> [] ->
    active_run_lengths rs2 <> [] ->
    canonical_normalized_pulse_classes rs1 <>
      canonical_normalized_pulse_classes rs2 ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs1) <>
      canonical_normalized_pulse_classes (scale_runs factor2 rs2).
Proof.
  intros factor1 factor2 rs1 rs2 Hfactor1 Hfactor2 Hactive1 Hactive2 Hneq Heq.
  apply Hneq.
  rewrite <- (canonical_normalized_pulse_classes_scale_invariant factor1 rs1 Hfactor1 Hactive1).
  rewrite <- (canonical_normalized_pulse_classes_scale_invariant factor2 rs2 Hfactor2 Hactive2).
  exact Heq.
Qed.

Theorem canonical_normalized_pulse_classes_equal_but_bases_ordered :
  forall factor1 factor2 rs,
    0 < factor1 ->
    factor1 < factor2 ->
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs factor1 rs) =
      canonical_normalized_pulse_classes (scale_runs factor2 rs) /\
    canonical_pulse_base_from_runs (scale_runs factor1 rs) <
      canonical_pulse_base_from_runs (scale_runs factor2 rs).
Proof.
  intros factor1 factor2 rs Hfactor1 Hlt Hpos Hactive.
  split.
  - apply canonical_normalized_pulse_classes_pairwise_scale_equal.
    + exact Hfactor1.
    + lia.
    + exact Hactive.
  - rewrite pulse_base_from_runs_canonical.
    rewrite pulse_base_from_runs_canonical.
    apply pulse_base_from_runs_scale_strict_order.
    + exact Hlt.
    + exact Hpos.
    + exact Hactive.
Qed.

Corollary canonical_normalized_pulse_classes_double_triple_same_but_bases_ordered :
  forall rs,
    runs_positive rs = true ->
    active_run_lengths rs <> [] ->
    canonical_normalized_pulse_classes (scale_runs 2 rs) =
      canonical_normalized_pulse_classes (scale_runs 3 rs) /\
    canonical_pulse_base_from_runs (scale_runs 2 rs) <
      canonical_pulse_base_from_runs (scale_runs 3 rs).
Proof.
  intros rs Hpos Hactive.
  apply canonical_normalized_pulse_classes_equal_but_bases_ordered.
  - lia.
  - lia.
  - exact Hpos.
  - exact Hactive.
Qed.

Definition CanonicalRFObject := list PulseClass.

Definition canonical_rf_object_from_runs (rs : Runs) : CanonicalRFObject :=
  canonical_normalized_pulse_classes rs.

Definition CoarseCanonicalRFObject := list CoarsePulseClass.

Definition coarse_canonical_rf_object_from_runs (rs : Runs) : CoarseCanonicalRFObject :=
  coarse_pulse_classes (canonical_rf_object_from_runs rs).

Definition tx_family_member (base_pattern : Runs) (te : nat) : Runs :=
  scale_runs te base_pattern.

Definition tx_family_object (base_pattern : Runs) : CanonicalRFObject :=
  canonical_rf_object_from_runs base_pattern.

Record FamilyDescriptor := {
  family_object : CanonicalRFObject;
  family_frame_bits : list bool
}.

Record FamilySemanticTower := {
  tower_object : CanonicalRFObject;
  tower_bits : list bool;
  tower_word : nat;
  tower_packet24 : Packet24
}.

Definition family_descriptor_from_runs (rs : Runs) : FamilyDescriptor :=
  {| family_object := canonical_rf_object_from_runs rs;
     family_frame_bits := canonical_frame_bits_from_runs rs |}.

Definition tx_family_descriptor (base_pattern : Runs) : FamilyDescriptor :=
  family_descriptor_from_runs base_pattern.

Definition semantic_tower_from_runs (rs : Runs) : FamilySemanticTower :=
  {| tower_object := canonical_rf_object_from_runs rs;
     tower_bits := canonical_frame_bits_from_runs rs;
     tower_word := canonical_frame_word_from_runs rs;
     tower_packet24 := canonical_packet24_from_runs rs |}.

Definition tx_family_semantic_tower (base_pattern : Runs) : FamilySemanticTower :=
  semantic_tower_from_runs base_pattern.

Theorem tx_family_canonical_object_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te) =
      tx_family_object base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member, tx_family_object.
  apply canonical_normalized_pulse_classes_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_frame_bits_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_frame_bits_from_runs (tx_family_member base_pattern te) =
      canonical_frame_bits_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_frame_bits_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_frame_word_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_frame_word_from_runs (tx_family_member base_pattern te) =
      canonical_frame_word_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_frame_word_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_descriptor_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    family_descriptor_from_runs (tx_family_member base_pattern te) =
      tx_family_descriptor base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold family_descriptor_from_runs, tx_family_descriptor.
  rewrite tx_family_canonical_object_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_bits_law by exact Hte || exact Hactive.
  reflexivity.
Qed.

Theorem tx_family_packet24_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_from_runs (tx_family_member base_pattern te) =
      canonical_packet24_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_packet24_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_tower_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    semantic_tower_from_runs (tx_family_member base_pattern te) =
      tx_family_semantic_tower base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold semantic_tower_from_runs, tx_family_semantic_tower.
  rewrite tx_family_canonical_object_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_bits_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_word_law by exact Hte || exact Hactive.
  rewrite tx_family_packet24_law by exact Hte || exact Hactive.
  reflexivity.
Qed.

Corollary tx_family_members_share_canonical_object :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te1) =
      canonical_rf_object_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member.
  apply canonical_normalized_pulse_classes_pairwise_scale_equal.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive.
Qed.

Corollary tx_family_members_share_packet24 :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_from_runs (tx_family_member base_pattern te1) =
      canonical_packet24_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  transitivity (canonical_packet24_from_runs base_pattern).
  - apply tx_family_packet24_law.
    + exact Hte1.
    + exact Hactive.
  - symmetry.
    apply tx_family_packet24_law.
    + exact Hte2.
    + exact Hactive.
Qed.

Theorem tx_family_object_and_base_order_law :
  forall base_pattern te1 te2,
    0 < te1 ->
    te1 < te2 ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te1) =
      canonical_rf_object_from_runs (tx_family_member base_pattern te2) /\
    canonical_pulse_base_from_runs (tx_family_member base_pattern te1) <
      canonical_pulse_base_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hlt Hpos Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member.
  apply canonical_normalized_pulse_classes_equal_but_bases_ordered.
  - exact Hte1.
  - exact Hlt.
  - exact Hpos.
  - exact Hactive.
Qed.

Theorem tx_families_with_distinct_objects_stay_separated :
  forall base_pattern1 base_pattern2 te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern1 <> [] ->
    active_run_lengths base_pattern2 <> [] ->
    tx_family_object base_pattern1 <> tx_family_object base_pattern2 ->
    canonical_rf_object_from_runs (tx_family_member base_pattern1 te1) <>
      canonical_rf_object_from_runs (tx_family_member base_pattern2 te2).
Proof.
  intros base_pattern1 base_pattern2 te1 te2 Hte1 Hte2 Hactive1 Hactive2 Hneq.
  unfold tx_family_object, canonical_rf_object_from_runs, tx_family_member in *.
  apply canonical_normalized_pulse_classes_scale_separated.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive1.
  - exact Hactive2.
  - exact Hneq.
Qed.

Fixpoint strictly_increasing (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      match xs' with
      | [] => True
      | y :: _ => x < y /\ strictly_increasing xs'
      end
  end.

Definition predicted_tx_family_objects
    (base_pattern : Runs)
    (tes : list nat)
    : list CanonicalRFObject :=
  map (fun te => canonical_rf_object_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_bases
    (base_pattern : Runs)
    (tes : list nat)
    : list nat :=
  map (fun te => canonical_pulse_base_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_frame_words
    (base_pattern : Runs)
    (tes : list nat)
    : list nat :=
  map (fun te => canonical_frame_word_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_packets
    (base_pattern : Runs)
    (tes : list nat)
    : list Packet24 :=
  map (fun te => canonical_packet24_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_towers
    (base_pattern : Runs)
    (tes : list nat)
    : list FamilySemanticTower :=
  map (fun te => semantic_tower_from_runs (tx_family_member base_pattern te)) tes.

Record TxSweepPrediction := {
  sweep_prediction_object : CanonicalRFObject;
  sweep_prediction_bases : list nat
}.

Record TxSweepSemanticPrediction := {
  semantic_prediction_object : CanonicalRFObject;
  semantic_prediction_bits : list bool;
  semantic_prediction_word : nat;
  semantic_prediction_packet24 : Packet24;
  semantic_prediction_bases : list nat
}.

Definition tx_family_sweep_prediction
    (base_pattern : Runs)
    (tes : list nat)
    : TxSweepPrediction :=
  {| sweep_prediction_object := tx_family_object base_pattern;
     sweep_prediction_bases := predicted_tx_family_bases base_pattern tes |}.

Definition tx_family_semantic_prediction
    (base_pattern : Runs)
    (tes : list nat)
    : TxSweepSemanticPrediction :=
  {| semantic_prediction_object := tx_family_object base_pattern;
     semantic_prediction_bits := canonical_frame_bits_from_runs base_pattern;
     semantic_prediction_word := canonical_frame_word_from_runs base_pattern;
     semantic_prediction_packet24 := canonical_packet24_from_runs base_pattern;
     semantic_prediction_bases := predicted_tx_family_bases base_pattern tes |}.

Theorem predicted_tx_family_objects_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_objects base_pattern tes =
      repeat (tx_family_object base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_canonical_object_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_frame_words_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_frame_words base_pattern tes =
      repeat (canonical_frame_word_from_runs base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_frame_word_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_packets_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_packets base_pattern tes =
      repeat (canonical_packet24_from_runs base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_packet24_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_towers_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_towers base_pattern tes =
      repeat (tx_family_semantic_tower base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_semantic_tower_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_bases_strictly_increasing :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    strictly_increasing tes ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    strictly_increasing (predicted_tx_family_bases base_pattern tes).
Proof.
  intros base_pattern tes Htes.
  induction tes as [|te1 tes IH]; intros Hinc Hpos Hactive; simpl in *.
  - exact I.
  - destruct tes as [|te2 tes']; simpl in *.
    + exact I.
    + inversion Htes as [|? ? Hte1 Htes']; subst.
      destruct Hinc as [Hlt Hinc'].
      split.
      * destruct
          (tx_family_object_and_base_order_law
             base_pattern te1 te2 Hte1 Hlt Hpos Hactive) as [_ Hbase].
        exact Hbase.
      * apply IH.
        -- exact Htes'.
        -- exact Hinc'.
        -- exact Hpos.
        -- exact Hactive.
Qed.

Theorem tx_family_sweep_prediction_objects_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_objects base_pattern tes =
      repeat
        (sweep_prediction_object (tx_family_sweep_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_sweep_prediction.
  simpl.
  apply predicted_tx_family_objects_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_sweep_prediction_bases_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    strictly_increasing tes ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    strictly_increasing
      (sweep_prediction_bases (tx_family_sweep_prediction base_pattern tes)).
Proof.
  intros base_pattern tes Htes Hinc Hpos Hactive.
  unfold tx_family_sweep_prediction.
  simpl.
  apply predicted_tx_family_bases_strictly_increasing.
  - exact Htes.
  - exact Hinc.
  - exact Hpos.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_words_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_frame_words base_pattern tes =
      repeat
        (semantic_prediction_word (tx_family_semantic_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_semantic_prediction.
  apply predicted_tx_family_frame_words_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_packets_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_packets base_pattern tes =
      repeat
        (semantic_prediction_packet24 (tx_family_semantic_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_semantic_prediction.
  apply predicted_tx_family_packets_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_towers_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_towers base_pattern tes =
      repeat
        (tx_family_semantic_tower base_pattern)
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  apply predicted_tx_family_towers_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Definition refined_detector_trace (factor : nat) (rs : Runs) : Trace :=
  flatten_runs (scale_runs factor rs).

Definition refined_detector_runs (factor : nat) (rs : Runs) : Runs :=
  rle_trace (refined_detector_trace factor rs).

Definition refined_detector_object (factor : nat) (rs : Runs) : CanonicalRFObject :=
  canonical_normalized_pulse_classes (refined_detector_runs factor rs).

Theorem refined_detector_runs_exact :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    refined_detector_runs factor rs = scale_runs factor rs.
Proof.
  intros factor rs Hfactor Hpos Halt.
  unfold refined_detector_runs, refined_detector_trace.
  rewrite rle_trace_flatten_runs_well_formed.
  - reflexivity.
  - apply runs_positive_scale.
    + exact Hfactor.
    + exact Hpos.
  - apply runs_alternating_scale.
    exact Halt.
Qed.

Theorem refined_detector_recovers_canonical_object :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    active_run_lengths rs <> [] ->
    refined_detector_object factor rs = canonical_rf_object_from_runs rs.
Proof.
  intros factor rs Hfactor Hpos Halt Hactive.
  unfold refined_detector_object, canonical_rf_object_from_runs.
  rewrite refined_detector_runs_exact.
  - apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor.
    + exact Hactive.
  - exact Hfactor.
  - exact Hpos.
  - exact Halt.
Qed.

Corollary refined_detector_pairwise_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    active_run_lengths rs <> [] ->
    refined_detector_object factor1 rs = refined_detector_object factor2 rs.
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hpos Halt Hactive.
  transitivity (canonical_rf_object_from_runs rs).
  - apply refined_detector_recovers_canonical_object.
    + exact Hfactor1.
    + exact Hpos.
    + exact Halt.
    + exact Hactive.
  - symmetry.
    apply refined_detector_recovers_canonical_object.
    + exact Hfactor2.
    + exact Hpos.
    + exact Halt.
    + exact Hactive.
Qed.

Definition EmitterClass := CanonicalRFObject.

Definition emitter_class_from_runs (rs : Runs) : EmitterClass :=
  canonical_rf_object_from_runs rs.

Definition same_emitter_class_runs (rs1 rs2 : Runs) : Prop :=
  emitter_class_from_runs rs1 = emitter_class_from_runs rs2.

Definition emitter_classes_separated_runs (rs1 rs2 : Runs) : Prop :=
  emitter_class_from_runs rs1 <> emitter_class_from_runs rs2.

Definition cross_receiver_invariant_runs (rs1 rs2 : Runs) : Prop :=
  canonical_rf_object_from_runs rs1 = canonical_rf_object_from_runs rs2.

Definition coarse_cross_receiver_invariant_runs (rs1 rs2 : Runs) : Prop :=
  coarse_canonical_rf_object_from_runs rs1 =
    coarse_canonical_rf_object_from_runs rs2.

Theorem same_emitter_class_runs_refl :
  forall rs,
    same_emitter_class_runs rs rs.
Proof.
  intro rs.
  unfold same_emitter_class_runs.
  reflexivity.
Qed.

Theorem same_emitter_class_runs_sym :
  forall rs1 rs2,
    same_emitter_class_runs rs1 rs2 ->
    same_emitter_class_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold same_emitter_class_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem same_emitter_class_runs_trans :
  forall rs1 rs2 rs3,
    same_emitter_class_runs rs1 rs2 ->
    same_emitter_class_runs rs2 rs3 ->
    same_emitter_class_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold same_emitter_class_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_refl :
  forall rs,
    cross_receiver_invariant_runs rs rs.
Proof.
  intro rs.
  unfold cross_receiver_invariant_runs.
  reflexivity.
Qed.

Theorem cross_receiver_invariant_runs_sym :
  forall rs1 rs2,
    cross_receiver_invariant_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold cross_receiver_invariant_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem cross_receiver_invariant_runs_trans :
  forall rs1 rs2 rs3,
    cross_receiver_invariant_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs2 rs3 ->
    cross_receiver_invariant_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold cross_receiver_invariant_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_from_same_emitter_class :
  forall rs1 rs2,
    same_emitter_class_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hsame.
  unfold same_emitter_class_runs, emitter_class_from_runs in Hsame.
  unfold cross_receiver_invariant_runs, canonical_rf_object_from_runs.
  exact Hsame.
Qed.

Theorem cross_receiver_invariant_runs_separated :
  forall rs1 rs2,
    canonical_rf_object_from_runs rs1 <> canonical_rf_object_from_runs rs2 ->
    ~ cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hneq Hsame.
  unfold cross_receiver_invariant_runs in Hsame.
  apply Hneq.
  exact Hsame.
Qed.

Theorem coarse_cross_receiver_invariant_runs_refl :
  forall rs,
    coarse_cross_receiver_invariant_runs rs rs.
Proof.
  intro rs.
  unfold coarse_cross_receiver_invariant_runs.
  reflexivity.
Qed.

Theorem coarse_cross_receiver_invariant_runs_sym :
  forall rs1 rs2,
    coarse_cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold coarse_cross_receiver_invariant_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem coarse_cross_receiver_invariant_runs_trans :
  forall rs1 rs2 rs3,
    coarse_cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs2 rs3 ->
    coarse_cross_receiver_invariant_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold coarse_cross_receiver_invariant_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_implies_coarse :
  forall rs1 rs2,
    cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hsame.
  unfold cross_receiver_invariant_runs in Hsame.
  unfold coarse_cross_receiver_invariant_runs, coarse_canonical_rf_object_from_runs.
  rewrite Hsame.
  reflexivity.
Qed.

Corollary tx_family_members_share_emitter_class :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    same_emitter_class_runs
      (tx_family_member base_pattern te1)
      (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  unfold same_emitter_class_runs, emitter_class_from_runs.
  apply tx_family_members_share_canonical_object.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive.
Qed.

Corollary tx_families_with_distinct_objects_have_separated_classes :
  forall base_pattern1 base_pattern2 te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern1 <> [] ->
    active_run_lengths base_pattern2 <> [] ->
    tx_family_object base_pattern1 <> tx_family_object base_pattern2 ->
    emitter_classes_separated_runs
      (tx_family_member base_pattern1 te1)
      (tx_family_member base_pattern2 te2).
Proof.
  intros base_pattern1 base_pattern2 te1 te2 Hte1 Hte2 Hactive1 Hactive2 Hneq.
  unfold emitter_classes_separated_runs, emitter_class_from_runs.
  apply tx_families_with_distinct_objects_stay_separated.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive1.
  - exact Hactive2.
  - exact Hneq.
Qed.

Theorem classify_run_with_base_mark_short_sound :
  forall base n,
    classify_run_with_base base (true, n) = MarkShort ->
    n < 2 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - inversion H; subst.
    apply Nat.ltb_lt in Hlt.
    exact Hlt.
  - discriminate.
Qed.

Theorem classify_run_with_base_mark_long_sound :
  forall base n,
    classify_run_with_base base (true, n) = MarkLong ->
    2 * base <= n.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - discriminate.
  - inversion H; subst.
    apply Nat.ltb_ge in Hlt.
    exact Hlt.
Qed.

Theorem classify_run_with_base_gap_short_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapShort ->
    n < 2 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - inversion H; subst.
    apply Nat.ltb_lt in Hlt.
    exact Hlt.
  - destruct (Nat.ltb n (10 * base)); discriminate.
Qed.

Theorem classify_run_with_base_gap_long_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapLong ->
    2 * base <= n /\ n < 10 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hshort.
  - discriminate.
  - destruct (Nat.ltb n (10 * base)) eqn:Hlong.
    + inversion H; subst.
      split.
      * apply Nat.ltb_ge in Hshort.
        exact Hshort.
      * apply Nat.ltb_lt in Hlong.
        exact Hlong.
    + discriminate.
Qed.

Theorem classify_run_with_base_gap_break_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapBreak ->
    10 * base <= n.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hshort.
  - discriminate.
  - destruct (Nat.ltb n (10 * base)) eqn:Hlong.
    + discriminate.
    + inversion H; subst.
      apply Nat.ltb_ge in Hlong.
      exact Hlong.
Qed.

Definition Power := nat.
Definition PowerTrace := list Power.

Fixpoint take_power (n : nat) (xs : PowerTrace) : PowerTrace :=
  match n, xs with
  | O, _ => []
  | S n', [] => []
  | S n', x :: xs' => x :: take_power n' xs'
  end.

Fixpoint drop_power (n : nat) (xs : PowerTrace) : PowerTrace :=
  match n, xs with
  | O, _ => xs
  | S n', [] => []
  | S n', _ :: xs' => drop_power n' xs'
  end.

Lemma take_drop_power :
  forall n xs,
    take_power n xs ++ drop_power n xs = xs.
Proof.
  induction n as [|n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Definition window_above_threshold (threshold sample : Power) : bool :=
  Nat.leb threshold sample.

Definition threshold_trace (threshold : Power) (xs : PowerTrace) : Trace :=
  map (window_above_threshold threshold) xs.

Definition active_count_from_powers
    (span threshold : nat)
    (xs : PowerTrace)
    : nat :=
  window_active_count span (threshold_trace threshold xs).

Definition first_dense_power_window
    (span threshold min_active : nat)
    (xs : PowerTrace)
    : option nat :=
  first_dense_window span min_active (threshold_trace threshold xs).

Definition has_dense_power_window
    (span threshold min_active : nat)
    (xs : PowerTrace)
    : bool :=
  match first_dense_power_window span threshold min_active xs with
  | Some _ => true
  | None => false
  end.

Definition first_active_power_window
    (threshold : nat)
    (xs : PowerTrace)
    : option nat :=
  first_true (threshold_trace threshold xs).

Definition last_active_power_window
    (threshold : nat)
    (xs : PowerTrace)
    : option nat :=
  last_true (threshold_trace threshold xs).

Definition pulse_runs_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Runs :=
  rle_trace (threshold_trace threshold xs).

Definition pulse_base_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  pulse_base_from_runs (pulse_runs_from_powers threshold xs).

Definition pulse_classes_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list PulseClass :=
  let rs := pulse_runs_from_powers threshold xs in
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Lemma drop_threshold_trace :
  forall n threshold xs,
    drop n (threshold_trace threshold xs) = threshold_trace threshold (drop_power n xs).
Proof.
  induction n as [|n IH]; intros threshold xs.
  - reflexivity.
  - destruct xs as [|x xs']; simpl.
    + reflexivity.
    + apply IH.
Qed.

Theorem first_dense_power_window_sound :
  forall span threshold min_active xs idx,
    first_dense_power_window span threshold min_active xs = Some idx ->
    idx <= length xs /\
    min_active <= active_count_from_powers span threshold (drop_power idx xs).
Proof.
  intros span threshold min_active xs idx H.
  unfold first_dense_power_window in H.
  destruct (first_dense_window_sound span min_active (threshold_trace threshold xs) idx H)
    as [Hidx Hcount].
  split.
  - unfold threshold_trace in Hidx.
    rewrite length_map in Hidx.
    exact Hidx.
  - unfold active_count_from_powers.
    rewrite <- drop_threshold_trace.
    exact Hcount.
Qed.

Theorem first_active_power_window_sound :
  forall threshold xs idx,
    first_active_power_window threshold xs = Some idx ->
    idx < length xs /\
    nth idx (threshold_trace threshold xs) false = true /\
    (forall j, j < idx -> nth j (threshold_trace threshold xs) false = false).
Proof.
  intros threshold xs idx H.
  unfold first_active_power_window in H.
  destruct (first_true_sound (threshold_trace threshold xs) idx H)
    as [Hlt [Hnth Hprefix]].
  split.
  - unfold threshold_trace in Hlt.
    rewrite length_map in Hlt.
    exact Hlt.
  - split.
    + exact Hnth.
    + exact Hprefix.
Qed.

Theorem last_active_power_window_sound :
  forall threshold xs idx,
    last_active_power_window threshold xs = Some idx ->
    idx < length xs /\
    nth idx (threshold_trace threshold xs) false = true /\
    (forall j,
        idx < j ->
        j < length xs ->
        nth j (threshold_trace threshold xs) false = false).
Proof.
  intros threshold xs idx H.
  unfold last_active_power_window in H.
  destruct (last_true_sound (threshold_trace threshold xs) idx H)
    as [Hlt [Hnth Hsuffix]].
  split.
  - unfold threshold_trace in Hlt.
    rewrite length_map in Hlt.
    exact Hlt.
  - split.
    + exact Hnth.
    + intros j Hij Hjlen.
      apply Hsuffix.
      * exact Hij.
      * unfold threshold_trace.
        rewrite length_map.
        exact Hjlen.
Qed.

Theorem flatten_pulse_runs_from_powers :
  forall threshold xs,
    flatten_runs (pulse_runs_from_powers threshold xs) = threshold_trace threshold xs.
Proof.
  intros threshold xs.
  unfold pulse_runs_from_powers.
  apply flatten_rle_trace.
Qed.

Theorem pulse_runs_from_powers_positive :
  forall threshold xs,
    runs_positive (pulse_runs_from_powers threshold xs) = true.
Proof.
  intros threshold xs.
  unfold pulse_runs_from_powers.
  apply rle_trace_positive.
Qed.

Theorem pulse_base_from_powers_positive :
  forall threshold xs,
    0 < pulse_base_from_powers threshold xs.
Proof.
  intros threshold xs.
  unfold pulse_base_from_powers.
  apply pulse_base_from_runs_positive.
  apply pulse_runs_from_powers_positive.
Qed.

Theorem pulse_classes_from_powers_length :
  forall threshold xs,
    length (pulse_classes_from_powers threshold xs) =
      length (pulse_runs_from_powers threshold xs).
Proof.
  intros threshold xs.
  unfold pulse_classes_from_powers.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem first_dense_power_window_complete_from_suffix :
  forall prefix suffix span threshold min_active,
    min_active <= active_count_from_powers span threshold suffix ->
    exists idx,
      first_dense_power_window span threshold min_active (prefix ++ suffix) = Some idx.
Proof.
  intros prefix suffix span threshold min_active Hcount.
  unfold first_dense_power_window, active_count_from_powers in *.
  unfold threshold_trace.
  rewrite map_app.
  apply first_dense_window_complete_from_suffix.
  exact Hcount.
Qed.

Corollary has_dense_power_window_complete_from_suffix :
  forall prefix suffix span threshold min_active,
    min_active <= active_count_from_powers span threshold suffix ->
    has_dense_power_window span threshold min_active (prefix ++ suffix) = true.
Proof.
  intros prefix suffix span threshold min_active Hcount.
  destruct
    (first_dense_power_window_complete_from_suffix
       prefix suffix span threshold min_active Hcount) as [idx Hidx].
  unfold has_dense_power_window.
  rewrite Hidx.
  reflexivity.
Qed.

Theorem first_dense_power_window_complete :
  forall prefix block suffix span threshold min_active,
    span <= length block ->
    min_active <= active_count_from_powers span threshold block ->
    exists idx,
      first_dense_power_window span threshold min_active (prefix ++ block ++ suffix) = Some idx.
Proof.
  intros prefix block suffix span threshold min_active Hspan Hdense.
  unfold first_dense_power_window, active_count_from_powers in *.
  unfold threshold_trace.
  rewrite map_app, map_app.
  eapply first_dense_window_complete.
  - rewrite length_map.
    exact Hspan.
  - exact Hdense.
Qed.

Theorem active_count_from_powers_threshold_monotone :
  forall span low high xs,
    low <= high ->
    active_count_from_powers span high xs <= active_count_from_powers span low xs.
Proof.
  induction span as [|span IH]; intros low high xs Hle.
  - unfold active_count_from_powers, window_active_count.
    simpl.
    lia.
  - unfold active_count_from_powers, window_active_count in *.
    destruct xs as [|x xs']; simpl.
    + apply Nat.le_refl.
    + unfold window_above_threshold.
      destruct (Nat.leb high x) eqn:Hhigh;
      destruct (Nat.leb low x) eqn:Hlow; simpl.
      * specialize (IH low high xs' Hle).
        lia.
      * apply Nat.leb_le in Hhigh.
        apply Nat.leb_gt in Hlow.
        lia.
      * eapply Nat.le_trans.
        -- apply IH.
           exact Hle.
        -- lia.
      * apply IH.
        exact Hle.
Qed.

Theorem has_dense_power_window_threshold_monotone :
  forall span low high min_active xs,
    low <= high ->
    has_dense_power_window span high min_active xs = true ->
    has_dense_power_window span low min_active xs = true.
Proof.
  intros span low high min_active xs Hle Hdetect.
  unfold has_dense_power_window in Hdetect.
  destruct (first_dense_power_window span high min_active xs) eqn:Hhigh.
  - apply first_dense_power_window_sound in Hhigh.
    destruct Hhigh as [Hidx Hcount].
    assert (Hmono :
      active_count_from_powers span high (drop_power n xs) <=
      active_count_from_powers span low (drop_power n xs)).
    {
      apply active_count_from_powers_threshold_monotone.
      exact Hle.
    }
    assert (Hlowcount :
      min_active <= active_count_from_powers span low (drop_power n xs)).
    {
      lia.
    }
    unfold has_dense_power_window.
    rewrite <- (take_drop_power n xs).
    apply has_dense_power_window_complete_from_suffix.
    exact Hlowcount.
  - discriminate.
Qed.

Definition scale_powers (factor : nat) (xs : PowerTrace) : PowerTrace :=
  map (Nat.mul factor) xs.

Definition offset_powers (offset : nat) (xs : PowerTrace) : PowerTrace :=
  map (Nat.add offset) xs.

Definition canonical_pulse_runs_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Runs :=
  canonical_runs (pulse_runs_from_powers threshold xs).

Definition canonical_pulse_base_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  canonical_pulse_base_from_runs (pulse_runs_from_powers threshold xs).

Definition canonical_pulse_classes_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list PulseClass :=
  canonical_normalized_pulse_classes (pulse_runs_from_powers threshold xs).

Definition canonical_frame_bits_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : list bool :=
  frame_bits_from_classes (canonical_pulse_classes_from_powers threshold xs).

Definition canonical_frame_word_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : nat :=
  bits_to_nat (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition power_within_margin (margin x y : nat) : Prop :=
  x <= y + margin /\ y <= x + margin.

Fixpoint power_trace_within_margin
    (margin : nat)
    (xs ys : PowerTrace)
    : Prop :=
  match xs, ys with
  | [], [] => True
  | x :: xs', y :: ys' =>
      power_within_margin margin x y /\
      power_trace_within_margin margin xs' ys'
  | _, _ => False
  end.

Definition threshold_stable_sample
    (threshold margin sample : nat)
    : Prop :=
  sample + margin < threshold \/ threshold + margin <= sample.

Fixpoint power_trace_threshold_stable
    (threshold margin : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_stable_sample threshold margin x /\
      power_trace_threshold_stable threshold margin xs'
  end.

Lemma window_above_threshold_scale_invariant :
  forall factor threshold sample,
    0 < factor ->
    window_above_threshold (factor * threshold) (factor * sample) =
      window_above_threshold threshold sample.
Proof.
  intros factor threshold sample Hfactor.
  unfold window_above_threshold.
  destruct (Nat.leb threshold sample) eqn:Hbase.
  - apply Nat.leb_le in Hbase.
    apply Nat.leb_le.
    apply (proj1 (Nat.mul_le_mono_pos_l threshold sample factor Hfactor)).
    exact Hbase.
  - apply Nat.leb_gt in Hbase.
    apply Nat.leb_gt.
    apply (proj1 (Nat.mul_lt_mono_pos_l factor sample threshold Hfactor)).
    exact Hbase.
Qed.

Theorem threshold_trace_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    threshold_trace (factor * threshold) (scale_powers factor xs) =
      threshold_trace threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite window_above_threshold_scale_invariant by exact Hfactor.
    rewrite IH by exact Hfactor.
    reflexivity.
Qed.

Theorem active_count_from_powers_scale_invariant :
  forall factor span threshold xs,
    0 < factor ->
    active_count_from_powers span (factor * threshold) (scale_powers factor xs) =
      active_count_from_powers span threshold xs.
Proof.
  intros factor span threshold xs Hfactor.
  unfold active_count_from_powers.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem first_dense_power_window_scale_invariant :
  forall factor span threshold min_active xs,
    0 < factor ->
    first_dense_power_window span (factor * threshold) min_active
      (scale_powers factor xs) =
      first_dense_power_window span threshold min_active xs.
Proof.
  intros factor span threshold min_active xs Hfactor.
  unfold first_dense_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem first_active_power_window_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    first_active_power_window (factor * threshold) (scale_powers factor xs) =
      first_active_power_window threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold first_active_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem last_active_power_window_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    last_active_power_window (factor * threshold) (scale_powers factor xs) =
      last_active_power_window threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold last_active_power_window.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem pulse_runs_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    pulse_runs_from_powers (factor * threshold) (scale_powers factor xs) =
      pulse_runs_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold pulse_runs_from_powers.
  rewrite threshold_trace_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_runs_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_runs_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_runs_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_runs_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_base_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_base_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_base_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_base_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_pulse_classes_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_pulse_classes_from_powers.
  rewrite pulse_runs_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Lemma window_above_threshold_offset_invariant :
  forall offset threshold sample,
    window_above_threshold (offset + threshold) (offset + sample) =
      window_above_threshold threshold sample.
Proof.
  intros offset threshold sample.
  unfold window_above_threshold.
  destruct (Nat.leb threshold sample) eqn:Hbase.
  - apply Nat.leb_le in Hbase.
    apply Nat.leb_le.
    lia.
  - apply Nat.leb_gt in Hbase.
    apply Nat.leb_gt.
    lia.
Qed.

Theorem threshold_trace_offset_invariant :
  forall offset threshold xs,
    threshold_trace (offset + threshold) (offset_powers offset xs) =
      threshold_trace threshold xs.
Proof.
  intros offset threshold xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite window_above_threshold_offset_invariant.
    rewrite IH.
    reflexivity.
Qed.

Theorem pulse_runs_from_powers_offset_invariant :
  forall offset threshold xs,
    pulse_runs_from_powers (offset + threshold) (offset_powers offset xs) =
      pulse_runs_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold pulse_runs_from_powers.
  rewrite threshold_trace_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_pulse_classes_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_pulse_classes_from_powers.
  rewrite pulse_runs_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_frame_bits_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite canonical_pulse_classes_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_frame_bits_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite canonical_pulse_classes_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_frame_word_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_scale_invariant by exact Hfactor.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_frame_word_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Lemma window_above_threshold_margin_invariant :
  forall threshold margin x y,
    power_within_margin margin x y ->
    threshold_stable_sample threshold margin x ->
    window_above_threshold threshold y =
      window_above_threshold threshold x.
Proof.
  intros threshold margin x y [Hxy Hyx] Hstable.
  destruct Hstable as [Hbelow | Habove].
  - assert (Hx : window_above_threshold threshold x = false).
    {
      unfold window_above_threshold.
      apply Nat.leb_gt.
      lia.
    }
    assert (Hy : window_above_threshold threshold y = false).
    {
      unfold window_above_threshold.
      apply Nat.leb_gt.
      lia.
    }
    rewrite Hx, Hy.
    reflexivity.
  - assert (Hx : window_above_threshold threshold x = true).
    {
      unfold window_above_threshold.
      apply Nat.leb_le.
      lia.
    }
    assert (Hy : window_above_threshold threshold y = true).
    {
      unfold window_above_threshold.
      apply Nat.leb_le.
      lia.
    }
    rewrite Hx, Hy.
    reflexivity.
Qed.

Theorem threshold_trace_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    threshold_trace threshold ys = threshold_trace threshold xs.
Proof.
  intros threshold margin xs.
  induction xs as [|x xs IH]; intros ys Hmargin Hstable.
  - destruct ys as [|y ys']; simpl in *.
    + reflexivity.
    + contradiction.
  - destruct ys as [|y ys']; simpl in *.
    + contradiction.
    + destruct Hmargin as [Hxy Hmargin'].
      destruct Hstable as [Hxstable Hstable'].
      rewrite (window_above_threshold_margin_invariant
                 threshold margin x y Hxy Hxstable).
      rewrite (IH ys' Hmargin' Hstable').
      reflexivity.
Qed.

Theorem first_dense_power_window_margin_invariant :
  forall span threshold margin xs ys min_active,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    first_dense_power_window span threshold min_active ys =
      first_dense_power_window span threshold min_active xs.
Proof.
  intros span threshold margin xs ys min_active Hmargin Hstable.
  unfold first_dense_power_window.
  rewrite (threshold_trace_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem pulse_runs_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    pulse_runs_from_powers threshold ys = pulse_runs_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold pulse_runs_from_powers.
  rewrite (threshold_trace_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_pulse_classes_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_pulse_classes_from_powers threshold ys =
      canonical_pulse_classes_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_pulse_classes_from_powers.
  rewrite (pulse_runs_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_frame_bits_from_powers threshold ys =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes.
  rewrite (canonical_pulse_classes_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_frame_word_from_powers threshold ys =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_from_powers threshold ys =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Definition Byte := nat.
Definition ByteStream := list Byte.
Definition IQPair := (Byte * Byte)%type.
Definition IQTrace := list IQPair.

Fixpoint bytes_to_iq (xs : ByteStream) : IQTrace :=
  match xs with
  | i :: q :: xs' => (i, q) :: bytes_to_iq xs'
  | _ => []
  end.

Definition centered_twice_abs (b : Byte) : nat :=
  let doubled := b + b in
  if Nat.leb doubled 255 then 255 - doubled else doubled - 255.

Definition iq_pair_energy (pair : IQPair) : Power :=
  let '(i, q) := pair in
  let di := centered_twice_abs i in
  let dq := centered_twice_abs q in
  di * di + dq * dq.

Definition iq_byte_pair_energy (i q : Byte) : Power :=
  let di := centered_twice_abs i in
  let dq := centered_twice_abs q in
  di * di + dq * dq.

Definition iq_energy_trace (xs : ByteStream) : PowerTrace :=
  map iq_pair_energy (bytes_to_iq xs).

Fixpoint sum_powers (xs : PowerTrace) : Power :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_powers xs'
  end.

Fixpoint power_window_sums_fuel
    (fuel window_pairs : nat)
    (xs : PowerTrace)
    : PowerTrace :=
  match fuel with
  | O => []
  | S fuel' =>
      match window_pairs with
      | O => []
      | S _ =>
          if Nat.ltb (length xs) window_pairs then
            []
          else
            sum_powers (take_power window_pairs xs)
              :: power_window_sums_fuel fuel' window_pairs (drop_power window_pairs xs)
      end
  end.

Definition power_window_sums (window_pairs : nat) (xs : PowerTrace) : PowerTrace :=
  power_window_sums_fuel (length xs) window_pairs xs.

Fixpoint iq_window_energy_trace_acc
    (window_pairs remaining acc : nat)
    (xs : ByteStream)
    (rev_windows : PowerTrace)
    : PowerTrace :=
  match xs with
  | i :: q :: xs' =>
      match remaining with
      | O => rev rev_windows
      | S remaining' =>
          let acc' := acc + iq_byte_pair_energy i q in
          match remaining' with
          | O =>
              iq_window_energy_trace_acc window_pairs window_pairs 0 xs'
                (acc' :: rev_windows)
          | S _ =>
              iq_window_energy_trace_acc window_pairs remaining' acc' xs'
                rev_windows
          end
      end
  | _ => rev rev_windows
  end.

Definition iq_window_energy_trace
    (window_pairs : nat)
    (xs : ByteStream)
    : PowerTrace :=
  match window_pairs with
  | O => []
  | S _ => iq_window_energy_trace_acc window_pairs window_pairs 0 xs []
  end.

Definition first_dense_iq_window
    (window_pairs span threshold min_active : nat)
    (xs : ByteStream)
    : option nat :=
  first_dense_power_window span threshold min_active
    (iq_window_energy_trace window_pairs xs).

Definition has_dense_iq_window
    (window_pairs span threshold min_active : nat)
    (xs : ByteStream)
    : bool :=
  has_dense_power_window span threshold min_active
    (iq_window_energy_trace window_pairs xs).

Definition first_active_iq_window
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : option nat :=
  first_active_power_window threshold
    (iq_window_energy_trace window_pairs xs).

Definition last_active_iq_window
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : option nat :=
  last_active_power_window threshold
    (iq_window_energy_trace window_pairs xs).

Definition pulse_runs_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Runs :=
  pulse_runs_from_powers threshold
    (iq_window_energy_trace window_pairs xs).

Definition pulse_base_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  pulse_base_from_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition pulse_classes_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PulseClass :=
  let rs := pulse_runs_from_iq window_pairs threshold xs in
  classify_runs_with_base (pulse_base_from_runs rs) rs.

Definition canonical_pulse_runs_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Runs :=
  canonical_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_pulse_base_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  canonical_pulse_base_from_runs (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_pulse_classes_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PulseClass :=
  canonical_normalized_pulse_classes (pulse_runs_from_iq window_pairs threshold xs).

Definition canonical_frame_bits_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list bool :=
  frame_bits_from_classes (canonical_pulse_classes_from_iq window_pairs threshold xs).

Definition canonical_frame_word_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : nat :=
  bits_to_nat (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24 :=
  packet24_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition emitter_class_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : EmitterClass :=
  canonical_pulse_classes_from_iq window_pairs threshold xs.

Definition same_emitter_class_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  emitter_class_from_iq window_pairs threshold xs =
    emitter_class_from_iq window_pairs threshold ys.

Definition cross_receiver_invariant_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  canonical_pulse_classes_from_iq window_pairs threshold xs =
    canonical_pulse_classes_from_iq window_pairs threshold ys.

Definition coarse_cross_receiver_invariant_iq
    (window_pairs threshold : nat)
    (xs ys : ByteStream)
    : Prop :=
  coarse_pulse_classes (canonical_pulse_classes_from_iq window_pairs threshold xs) =
    coarse_pulse_classes (canonical_pulse_classes_from_iq window_pairs threshold ys).

Definition pulse_class_eqb (x y : PulseClass) : bool :=
  match x, y with
  | MarkShort, MarkShort => true
  | MarkLong, MarkLong => true
  | GapShort, GapShort => true
  | GapLong, GapLong => true
  | GapBreak, GapBreak => true
  | _, _ => false
  end.

Fixpoint pulse_class_list_eqb
    (xs ys : list PulseClass)
    : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      pulse_class_eqb x y && pulse_class_list_eqb xs' ys'
  | _, _ => false
  end.

Record PulseParseCertificate := {
  certificate_window_pairs : nat;
  certificate_threshold : nat;
  certificate_first_active : option nat;
  certificate_last_active : option nat;
  certificate_runs : Runs;
  certificate_base : nat;
  certificate_classes : list PulseClass
}.

Record FrameParseCertificate := {
  frame_certificate_pulse : PulseParseCertificate;
  frame_certificate_bits : list bool
}.

Definition pulse_parse_certificate_self_consistent
    (cert : PulseParseCertificate)
    : bool :=
  Nat.eqb (certificate_base cert)
    (pulse_base_from_runs (certificate_runs cert))
  &&
  Nat.eqb (length (certificate_classes cert))
    (length (certificate_runs cert))
  &&
  pulse_class_list_eqb
    (certificate_classes cert)
    (classify_runs_with_base
      (certificate_base cert)
      (certificate_runs cert)).

Definition certify_canonical_pulse_parse_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : PulseParseCertificate :=
  let runs := canonical_pulse_runs_from_iq window_pairs threshold xs in
  let base := canonical_pulse_base_from_iq window_pairs threshold xs in
  let classes := canonical_pulse_classes_from_iq window_pairs threshold xs in
  {| certificate_window_pairs := window_pairs;
     certificate_threshold := threshold;
     certificate_first_active :=
       first_active_iq_window window_pairs threshold xs;
     certificate_last_active :=
       last_active_iq_window window_pairs threshold xs;
     certificate_runs := runs;
     certificate_base := base;
     certificate_classes := classes |}.

Definition certify_canonical_frame_parse_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FrameParseCertificate :=
  let pulse_cert := certify_canonical_pulse_parse_from_iq window_pairs threshold xs in
  {| frame_certificate_pulse := pulse_cert;
     frame_certificate_bits :=
       canonical_frame_bits_from_iq window_pairs threshold xs |}.

Definition pulse_parse_certificate_valid
    (window_pairs threshold : nat)
    (xs : ByteStream)
    (cert : PulseParseCertificate)
    : Prop :=
  certificate_window_pairs cert = window_pairs /\
  certificate_threshold cert = threshold /\
  certificate_first_active cert =
    first_active_iq_window window_pairs threshold xs /\
  certificate_last_active cert =
    last_active_iq_window window_pairs threshold xs /\
  certificate_runs cert =
    canonical_pulse_runs_from_iq window_pairs threshold xs /\
  certificate_base cert =
    canonical_pulse_base_from_iq window_pairs threshold xs /\
  certificate_classes cert =
    canonical_pulse_classes_from_iq window_pairs threshold xs /\
  pulse_parse_certificate_self_consistent cert = true.

Definition frame_parse_certificate_valid
    (window_pairs threshold : nat)
    (xs : ByteStream)
    (cert : FrameParseCertificate)
    : Prop :=
  pulse_parse_certificate_valid
    window_pairs threshold xs (frame_certificate_pulse cert) /\
  frame_certificate_bits cert =
    canonical_frame_bits_from_iq window_pairs threshold xs.

Theorem first_dense_iq_window_sound :
  forall window_pairs span threshold min_active xs idx,
    first_dense_iq_window window_pairs span threshold min_active xs = Some idx ->
    idx <= length (iq_window_energy_trace window_pairs xs) /\
    min_active <=
      active_count_from_powers span threshold
        (drop_power idx (iq_window_energy_trace window_pairs xs)).
Proof.
  intros window_pairs span threshold min_active xs idx H.
  unfold first_dense_iq_window in H.
  apply first_dense_power_window_sound in H.
  exact H.
Qed.

Theorem first_active_iq_window_sound :
  forall window_pairs threshold xs idx,
    first_active_iq_window window_pairs threshold xs = Some idx ->
    idx < length (iq_window_energy_trace window_pairs xs) /\
    nth idx
      (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
      false = true /\
    (forall j,
        j < idx ->
        nth j
          (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
          false = false).
Proof.
  intros window_pairs threshold xs idx H.
  unfold first_active_iq_window in H.
  apply first_active_power_window_sound in H.
  exact H.
Qed.

Theorem last_active_iq_window_sound :
  forall window_pairs threshold xs idx,
    last_active_iq_window window_pairs threshold xs = Some idx ->
    idx < length (iq_window_energy_trace window_pairs xs) /\
    nth idx
      (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
      false = true /\
    (forall j,
        idx < j ->
        j < length (iq_window_energy_trace window_pairs xs) ->
        nth j
          (threshold_trace threshold (iq_window_energy_trace window_pairs xs))
          false = false).
Proof.
  intros window_pairs threshold xs idx H.
  unfold last_active_iq_window in H.
  apply last_active_power_window_sound in H.
  exact H.
Qed.

Theorem flatten_pulse_runs_from_iq :
  forall window_pairs threshold xs,
    flatten_runs (pulse_runs_from_iq window_pairs threshold xs) =
      threshold_trace threshold (iq_window_energy_trace window_pairs xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_runs_from_iq.
  apply flatten_pulse_runs_from_powers.
Qed.

Theorem pulse_runs_from_iq_positive :
  forall window_pairs threshold xs,
    runs_positive (pulse_runs_from_iq window_pairs threshold xs) = true.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_runs_from_iq.
  apply pulse_runs_from_powers_positive.
Qed.

Theorem pulse_base_from_iq_positive :
  forall window_pairs threshold xs,
    0 < pulse_base_from_iq window_pairs threshold xs.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_base_from_iq.
  apply pulse_base_from_runs_positive.
  apply pulse_runs_from_iq_positive.
Qed.

Theorem pulse_classes_from_iq_length :
  forall window_pairs threshold xs,
    length (pulse_classes_from_iq window_pairs threshold xs) =
      length (pulse_runs_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_classes_from_iq.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem canonical_pulse_base_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_pulse_base_from_iq window_pairs threshold xs =
      pulse_base_from_iq window_pairs threshold xs.
Proof.
  intros window_pairs threshold xs.
  unfold canonical_pulse_base_from_iq, pulse_base_from_iq.
  apply pulse_base_from_runs_canonical.
Qed.

Theorem canonical_pulse_classes_from_iq_length :
  forall window_pairs threshold xs,
    length (canonical_pulse_classes_from_iq window_pairs threshold xs) =
      length (canonical_pulse_runs_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold canonical_pulse_classes_from_iq, canonical_pulse_runs_from_iq.
  unfold canonical_normalized_pulse_classes, normalized_pulse_classes.
  rewrite classify_runs_with_base_length.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_frame_bits_from_iq window_pairs threshold xs =
      frame_bits_from_classes
        (canonical_pulse_classes_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_iq_eq :
  forall window_pairs threshold xs,
    canonical_frame_word_from_iq window_pairs threshold xs =
      bits_to_nat (canonical_frame_bits_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  reflexivity.
Qed.

Definition family_descriptor_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FamilyDescriptor :=
  {| family_object := canonical_pulse_classes_from_iq window_pairs threshold xs;
     family_frame_bits := canonical_frame_bits_from_iq window_pairs threshold xs |}.

Definition semantic_tower_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FamilySemanticTower :=
  {| tower_object := canonical_pulse_classes_from_iq window_pairs threshold xs;
     tower_bits := canonical_frame_bits_from_iq window_pairs threshold xs;
     tower_word := canonical_frame_word_from_iq window_pairs threshold xs;
     tower_packet24 := canonical_packet24_from_iq window_pairs threshold xs |}.

Definition observed_iq_matches_family
    (base_pattern : Runs)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Prop :=
  canonical_pulse_classes_from_iq window_pairs threshold xs =
    tx_family_object base_pattern.

Theorem observed_iq_matches_family_implies_frame_bits :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_frame_bits_from_iq window_pairs threshold xs =
      canonical_frame_bits_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold observed_iq_matches_family, tx_family_object in Hmatch.
  unfold canonical_frame_bits_from_iq, canonical_frame_bits_from_runs.
  rewrite Hmatch.
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_frame_word :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_frame_word_from_iq window_pairs threshold xs =
      canonical_frame_word_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_frame_word_from_iq, canonical_frame_word_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet24 :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet24_from_iq window_pairs threshold xs =
      canonical_packet24_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet24_from_iq, canonical_packet24_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_descriptor :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    family_descriptor_from_iq window_pairs threshold xs =
      tx_family_descriptor base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold family_descriptor_from_iq, tx_family_descriptor, family_descriptor_from_runs.
  rewrite Hmatch.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_semantic_tower :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    semantic_tower_from_iq window_pairs threshold xs =
      tx_family_semantic_tower base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold semantic_tower_from_iq, tx_family_semantic_tower, semantic_tower_from_runs.
  rewrite Hmatch.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_frame_word
             base_pattern window_pairs threshold xs Hmatch).
  rewrite (observed_iq_matches_family_implies_packet24
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_frame_bits_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_frame_bits_from_iq.
  rewrite Hclasses.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_frame_word_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_word_from_iq window_pairs1 threshold1 xs =
      canonical_frame_word_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_frame_word_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet24_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet24_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_frame_word_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_frame_word_from_iq window_pairs1 threshold1 xs =
      canonical_frame_word_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_frame_word_from_iq.
  rewrite class_invariant_between_iq_regimes_implies_frame_bits_invariant
    with (window_pairs1 := window_pairs1)
         (threshold1 := threshold1)
         (window_pairs2 := window_pairs2)
         (threshold2 := threshold2)
         (xs := xs).
  - reflexivity.
  - exact Hclasses.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet24_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet24_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_descriptor_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    family_descriptor_from_iq window_pairs1 threshold1 xs =
      family_descriptor_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold family_descriptor_from_iq.
  rewrite Hclasses.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_semantic_tower_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    semantic_tower_from_iq window_pairs1 threshold1 xs =
      semantic_tower_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold semantic_tower_from_iq.
  rewrite Hclasses.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_frame_word_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  rewrite (class_invariant_between_iq_regimes_implies_packet24_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem same_emitter_class_iq_refl :
  forall window_pairs threshold xs,
    same_emitter_class_iq window_pairs threshold xs xs.
Proof.
  intros window_pairs threshold xs.
  unfold same_emitter_class_iq.
  reflexivity.
Qed.

Theorem same_emitter_class_iq_sym :
  forall window_pairs threshold xs ys,
    same_emitter_class_iq window_pairs threshold xs ys ->
    same_emitter_class_iq window_pairs threshold ys xs.
Proof.
  intros window_pairs threshold xs ys Hsame.
  unfold same_emitter_class_iq in *.
  symmetry.
  exact Hsame.
Qed.

Theorem same_emitter_class_iq_trans :
  forall window_pairs threshold xs ys zs,
    same_emitter_class_iq window_pairs threshold xs ys ->
    same_emitter_class_iq window_pairs threshold ys zs ->
    same_emitter_class_iq window_pairs threshold xs zs.
Proof.
  intros window_pairs threshold xs ys zs Hxy Hyz.
  unfold same_emitter_class_iq in *.
  congruence.
Qed.

Inductive DeviceKind :=
| DeviceFlipper
| DeviceFpga
| DeviceRemote
| DeviceOther.

Record DeviceObservation := {
  observed_device_kind : DeviceKind;
  observed_window_pairs : nat;
  observed_threshold : nat;
  observed_iq : ByteStream
}.

Definition realized_emitter_class
    (obs : DeviceObservation)
    : EmitterClass :=
  emitter_class_from_iq
    (observed_window_pairs obs)
    (observed_threshold obs)
    (observed_iq obs).

Definition realizes_class
    (obs : DeviceObservation)
    (cls : EmitterClass)
    : Prop :=
  realized_emitter_class obs = cls.

Definition cross_device_realization
    (obs1 obs2 : DeviceObservation)
    : Prop :=
  realized_emitter_class obs1 = realized_emitter_class obs2.

Theorem cross_device_realization_refl :
  forall obs,
    cross_device_realization obs obs.
Proof.
  intro obs.
  unfold cross_device_realization.
  reflexivity.
Qed.

Theorem cross_device_realization_sym :
  forall obs1 obs2,
    cross_device_realization obs1 obs2 ->
    cross_device_realization obs2 obs1.
Proof.
  intros obs1 obs2 Hsame.
  unfold cross_device_realization in *.
  symmetry.
  exact Hsame.
Qed.

Theorem cross_device_realization_trans :
  forall obs1 obs2 obs3,
    cross_device_realization obs1 obs2 ->
    cross_device_realization obs2 obs3 ->
    cross_device_realization obs1 obs3.
Proof.
  intros obs1 obs2 obs3 H12 H23.
  unfold cross_device_realization in *.
  congruence.
Qed.

Theorem realizes_class_from_cross_device_realization :
  forall obs1 obs2 cls,
    realizes_class obs1 cls ->
    cross_device_realization obs1 obs2 ->
    realizes_class obs2 cls.
Proof.
  intros obs1 obs2 cls Hcls Hsame.
  unfold realizes_class, cross_device_realization in *.
  congruence.
Qed.

Theorem cross_device_realization_separated :
  forall obs1 obs2 cls1 cls2,
    realizes_class obs1 cls1 ->
    realizes_class obs2 cls2 ->
    cls1 <> cls2 ->
    ~ cross_device_realization obs1 obs2.
Proof.
  intros obs1 obs2 cls1 cls2 Hcls1 Hcls2 Hneq Hsame.
  unfold realizes_class, cross_device_realization in *.
  apply Hneq.
  congruence.
Qed.

Corollary flipper_fpga_remote_realization_transfer :
  forall window_pairs threshold xs ys zs cls,
    realizes_class
      {| observed_device_kind := DeviceFlipper;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := xs |}
      cls ->
    cross_device_realization
      {| observed_device_kind := DeviceFlipper;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := xs |}
      {| observed_device_kind := DeviceFpga;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := ys |} ->
    cross_device_realization
      {| observed_device_kind := DeviceFpga;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := ys |}
      {| observed_device_kind := DeviceRemote;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := zs |} ->
    realizes_class
      {| observed_device_kind := DeviceRemote;
         observed_window_pairs := window_pairs;
         observed_threshold := threshold;
         observed_iq := zs |}
      cls.
Proof.
  intros window_pairs threshold xs ys zs cls Hflipper Hflipper_fpga Hfpga_remote.
  eapply realizes_class_from_cross_device_realization.
  - eapply realizes_class_from_cross_device_realization.
    + exact Hflipper.
    + exact Hflipper_fpga.
  - exact Hfpga_remote.
Qed.

Lemma pulse_class_list_eqb_refl :
  forall xs,
    pulse_class_list_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct x; simpl; rewrite IH; reflexivity.
Qed.

Fixpoint bool_list_eqb (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Bool.eqb x y && bool_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma bool_list_eqb_refl :
  forall xs,
    bool_list_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite Bool.eqb_reflx.
    rewrite IH.
    reflexivity.
Qed.

Record ObservedFrame := {
  observed_class : EmitterClass;
  observed_counter : nat
}.

Definition SecurityState := list ObservedFrame.

Record ObservedDecodedFrame := {
  observed_bits : list bool;
  observed_bits_counter : nat
}.

Definition DecodedSecurityState := list ObservedDecodedFrame.

Definition option_max (x y : option nat) : option nat :=
  match x, y with
  | None, z => z
  | z, None => z
  | Some a, Some b => Some (Nat.max a b)
  end.

Fixpoint max_counter_for_bits
    (bits : list bool)
    (state : DecodedSecurityState)
    : option nat :=
  match state with
  | [] => None
  | frame :: state' =>
      let rest := max_counter_for_bits bits state' in
      if bool_list_eqb bits (observed_bits frame) then
        option_max (Some (observed_bits_counter frame)) rest
      else
        rest
  end.

Definition decoded_frame_fresh
    (state : DecodedSecurityState)
    (frame : ObservedDecodedFrame)
    : bool :=
  match max_counter_for_bits (observed_bits frame) state with
  | None => true
  | Some max_seen => Nat.ltb max_seen (observed_bits_counter frame)
  end.

Definition record_decoded_frame
    (state : DecodedSecurityState)
    (frame : ObservedDecodedFrame)
    : DecodedSecurityState :=
  frame :: state.

Fixpoint max_counter_for_class
    (cls : EmitterClass)
    (state : SecurityState)
    : option nat :=
  match state with
  | [] => None
  | frame :: state' =>
      let rest := max_counter_for_class cls state' in
      if pulse_class_list_eqb cls (observed_class frame) then
        option_max (Some (observed_counter frame)) rest
      else
        rest
  end.

Definition frame_fresh
    (state : SecurityState)
    (frame : ObservedFrame)
    : bool :=
  match max_counter_for_class (observed_class frame) state with
  | None => true
  | Some max_seen => Nat.ltb max_seen (observed_counter frame)
  end.

Definition record_frame
    (state : SecurityState)
    (frame : ObservedFrame)
    : SecurityState :=
  frame :: state.

Lemma max_counter_for_class_record_same :
  forall cls ctr state,
    max_counter_for_class cls
      (record_frame state {| observed_class := cls; observed_counter := ctr |}) =
      option_max (Some ctr) (max_counter_for_class cls state).
Proof.
  intros cls ctr state.
  unfold record_frame.
  simpl.
  rewrite pulse_class_list_eqb_refl.
  reflexivity.
Qed.

Lemma max_counter_for_bits_record_same :
  forall bits ctr state,
    max_counter_for_bits bits
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |}) =
      option_max (Some ctr) (max_counter_for_bits bits state).
Proof.
  intros bits ctr state.
  unfold record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  reflexivity.
Qed.

Lemma max_counter_for_class_record_different :
  forall cls cls' ctr state,
    pulse_class_list_eqb cls cls' = false ->
    max_counter_for_class cls
      (record_frame state {| observed_class := cls'; observed_counter := ctr |}) =
      max_counter_for_class cls state.
Proof.
  intros cls cls' ctr state Hneq.
  unfold record_frame.
  simpl.
  rewrite Hneq.
  reflexivity.
Qed.

Lemma max_counter_for_bits_record_different :
  forall bits bits' ctr state,
    bool_list_eqb bits bits' = false ->
    max_counter_for_bits bits
      (record_decoded_frame state
         {| observed_bits := bits'; observed_bits_counter := ctr |}) =
      max_counter_for_bits bits state.
Proof.
  intros bits bits' ctr state Hneq.
  unfold record_decoded_frame.
  simpl.
  rewrite Hneq.
  reflexivity.
Qed.

Theorem unseen_class_is_fresh :
  forall cls ctr state,
    max_counter_for_class cls state = None ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = true.
Proof.
  intros cls ctr state Hnone.
  unfold frame_fresh.
  simpl.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem unseen_bits_are_fresh :
  forall bits ctr state,
    max_counter_for_bits bits state = None ->
    decoded_frame_fresh
      state {| observed_bits := bits; observed_bits_counter := ctr |} = true.
Proof.
  intros bits ctr state Hnone.
  unfold decoded_frame_fresh.
  simpl.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem greater_counter_is_fresh :
  forall cls ctr state max_seen,
    max_counter_for_class cls state = Some max_seen ->
    max_seen < ctr ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = true.
Proof.
  intros cls ctr state max_seen Hmax Hlt.
  unfold frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem greater_counter_bits_are_fresh :
  forall bits ctr state max_seen,
    max_counter_for_bits bits state = Some max_seen ->
    max_seen < ctr ->
    decoded_frame_fresh
      state {| observed_bits := bits; observed_bits_counter := ctr |} = true.
Proof.
  intros bits ctr state max_seen Hmax Hlt.
  unfold decoded_frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem nonincreasing_counter_is_rejected :
  forall cls ctr state max_seen,
    max_counter_for_class cls state = Some max_seen ->
    ctr <= max_seen ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = false.
Proof.
  intros cls ctr state max_seen Hmax Hle.
  unfold frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_ge.
  exact Hle.
Qed.

Theorem exact_replay_rejected :
  forall cls ctr state,
    frame_fresh
      (record_frame state {| observed_class := cls; observed_counter := ctr |})
      {| observed_class := cls; observed_counter := ctr |} = false.
Proof.
  intros cls ctr state.
  unfold frame_fresh.
  rewrite max_counter_for_class_record_same.
  simpl.
  destruct (max_counter_for_class cls state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    lia.
Qed.

Theorem exact_decoded_replay_rejected :
  forall bits ctr state,
    decoded_frame_fresh
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |})
      {| observed_bits := bits; observed_bits_counter := ctr |} = false.
Proof.
  intros bits ctr state.
  unfold decoded_frame_fresh, record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  simpl.
  destruct (max_counter_for_bits bits state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    lia.
Qed.

Theorem recorded_frame_rejects_same_or_lower_counter :
  forall cls ctr ctr' state,
    ctr' <= ctr ->
    frame_fresh
      (record_frame state {| observed_class := cls; observed_counter := ctr |})
      {| observed_class := cls; observed_counter := ctr' |} = false.
Proof.
  intros cls ctr ctr' state Hle.
  unfold frame_fresh.
  rewrite max_counter_for_class_record_same.
  simpl.
  destruct (max_counter_for_class cls state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    eapply Nat.le_trans.
    + exact Hle.
    + apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    exact Hle.
Qed.

Theorem recorded_decoded_frame_rejects_same_or_lower_counter :
  forall bits ctr ctr' state,
    ctr' <= ctr ->
    decoded_frame_fresh
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |})
      {| observed_bits := bits; observed_bits_counter := ctr' |} = false.
Proof.
  intros bits ctr ctr' state Hle.
  unfold decoded_frame_fresh, record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  simpl.
  destruct (max_counter_for_bits bits state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    eapply Nat.le_trans.
    + exact Hle.
    + apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    exact Hle.
Qed.

Theorem certify_canonical_pulse_parse_from_iq_self_consistent :
  forall window_pairs threshold xs,
    pulse_parse_certificate_self_consistent
      (certify_canonical_pulse_parse_from_iq window_pairs threshold xs) = true.
Proof.
  intros window_pairs threshold xs.
  unfold pulse_parse_certificate_self_consistent.
  unfold certify_canonical_pulse_parse_from_iq.
  unfold canonical_pulse_base_from_iq, canonical_pulse_runs_from_iq.
  unfold canonical_pulse_classes_from_iq.
  unfold canonical_pulse_base_from_runs.
  unfold canonical_normalized_pulse_classes, normalized_pulse_classes.
  simpl.
  rewrite classify_runs_with_base_length.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite pulse_class_list_eqb_refl.
  reflexivity.
Qed.

Theorem certify_canonical_pulse_parse_from_iq_valid :
  forall window_pairs threshold xs,
    pulse_parse_certificate_valid
      window_pairs
      threshold
      xs
      (certify_canonical_pulse_parse_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold pulse_parse_certificate_valid.
  unfold certify_canonical_pulse_parse_from_iq.
  repeat split; try reflexivity.
  apply certify_canonical_pulse_parse_from_iq_self_consistent.
Qed.

Theorem certify_canonical_frame_parse_from_iq_valid :
  forall window_pairs threshold xs,
    frame_parse_certificate_valid
      window_pairs
      threshold
      xs
      (certify_canonical_frame_parse_from_iq window_pairs threshold xs).
Proof.
  intros window_pairs threshold xs.
  unfold frame_parse_certificate_valid.
  split.
  - apply certify_canonical_pulse_parse_from_iq_valid.
  - reflexivity.
Qed.

Example dense_window_positive_example :
  has_dense_window 5 3 [false; false; true; true; true; true; false] = true.
Proof.
  reflexivity.
Qed.

Example dense_window_negative_example :
  has_dense_window 5 4 [false; false; true; true; true; false; false] = false.
Proof.
  reflexivity.
Qed.

Example power_dense_window_positive_example :
  has_dense_power_window 5 10 3 [0; 0; 12; 14; 15; 15; 2] = true.
Proof.
  reflexivity.
Qed.

Example power_threshold_monotone_example :
  has_dense_power_window 5 10 3 [0; 0; 12; 14; 15; 15; 2] = true ->
  has_dense_power_window 5 8 3 [0; 0; 12; 14; 15; 15; 2] = true.
Proof.
  intro H.
  apply (has_dense_power_window_threshold_monotone 5 8 10 3
           [0; 0; 12; 14; 15; 15; 2]).
  - lia.
  - exact H.
Qed.

Example iq_energy_example :
  iq_energy_trace [255; 255; 128; 128] = [255 * 255 + 255 * 255; 2].
Proof.
  reflexivity.
Qed.

Example iq_window_energy_example :
  iq_window_energy_trace 2 [255; 255; 255; 255; 128; 128; 128; 128] =
    [2 * (255 * 255 + 255 * 255); 4].
Proof.
  reflexivity.
Qed.

Example iq_active_window_example :
  first_active_iq_window 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = Some 0 /\
  last_active_iq_window 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = Some 0.
Proof.
  split; reflexivity.
Qed.

Example iq_pulse_runs_example :
  pulse_runs_from_iq 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] = [(true, 1); (false, 1)].
Proof.
  reflexivity.
Qed.

Example iq_pulse_classes_example :
  pulse_classes_from_iq 2 (100 * 1000) [255; 255; 255; 255; 128; 128; 128; 128] =
    [MarkShort; GapShort].
Proof.
  reflexivity.
Qed.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "burst_detector_extracted.ml"
  count_active
  take
  drop
  window_active_count
  dense_window
  first_dense_window
  has_dense_window
  first_true
  last_true
  repeat_window
  flatten_runs
  rle_trace
  runs_positive
  active_run_lengths
  inactive_run_lengths
  min_list_default
  classify_run_with_base
  classify_runs_with_base
  pulse_base_from_runs
  window_above_threshold
  threshold_trace
  take_power
  drop_power
  active_count_from_powers
  first_dense_power_window
  has_dense_power_window
  first_active_power_window
  last_active_power_window
  pulse_runs_from_powers
  pulse_base_from_powers
  pulse_classes_from_powers
  bytes_to_iq
  centered_twice_abs
  iq_pair_energy
  iq_byte_pair_energy
  iq_energy_trace
  sum_powers
  power_window_sums
  iq_window_energy_trace
  first_dense_iq_window
  has_dense_iq_window
  first_active_iq_window
  last_active_iq_window
  pulse_runs_from_iq
  pulse_base_from_iq
  pulse_classes_from_iq
  pulse_class_eqb
  pulse_class_list_eqb
  frame_tokens_from_classes
  first_frame_bits_from_tokens
  frame_bits_from_classes
  bits_to_nat
  packet24_from_bits
  canonical_pulse_runs_from_iq
  canonical_pulse_base_from_iq
  canonical_pulse_classes_from_iq
  canonical_frame_bits_from_powers
  canonical_frame_bits_from_iq
  canonical_frame_word_from_powers
  canonical_frame_word_from_iq
  canonical_packet24_from_powers
  canonical_packet24_from_iq
  pulse_parse_certificate_self_consistent
  certify_canonical_pulse_parse_from_iq
  certify_canonical_frame_parse_from_iq.
