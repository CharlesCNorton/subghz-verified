From Stdlib Require Import List Bool Arith Lia.

Import ListNotations.

Require Import SubGhzCore SubGhzFamilies.

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

Definition canonical_packet24_byte_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24ByteView :=
  packet24_byte_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_nibble_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24NibbleView :=
  packet24_nibble_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet24_field_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : Packet24FieldView :=
  packet24_field_view_from_bits (canonical_frame_bits_from_powers threshold xs).

Definition canonical_packet_structure_view_from_powers
    (spec : PacketStructureSpec)
    (threshold : nat)
    (xs : PowerTrace)
    : list PacketStructuredFieldValue :=
  packet_structure_view_from_bits spec
    (canonical_frame_bits_from_powers threshold xs).

Definition canonical_field_counter_view_from_powers
    (schema : CounterSchema)
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  field_counter_view_from_bits schema (canonical_frame_bits_from_powers threshold xs).

Definition canonical_hi16_lo8_counter_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  canonical_field_counter_view_from_powers hi16_lo8_counter_schema threshold xs.

Definition canonical_prefix12_suffix12_counter_view_from_powers
    (threshold : nat)
    (xs : PowerTrace)
    : FieldCounterView :=
  canonical_field_counter_view_from_powers prefix12_suffix12_counter_schema threshold xs.

Definition canonical_field_counter_fresh_from_powers
    (schema : CounterSchema)
    (state : FieldCounterState)
    (threshold : nat)
    (xs : PowerTrace)
    : bool :=
  field_counter_fresh state (canonical_field_counter_view_from_powers schema threshold xs).

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

Definition threshold_shift_up_stable_sample
    (threshold drift sample : nat)
    : Prop :=
  sample < threshold \/ threshold + drift <= sample.

Fixpoint power_trace_threshold_shift_up_stable
    (threshold drift : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_shift_up_stable_sample threshold drift x /\
      power_trace_threshold_shift_up_stable threshold drift xs'
  end.

Definition threshold_shift_down_stable_sample
    (threshold drift sample : nat)
    : Prop :=
  sample + drift < threshold \/ threshold <= sample.

Fixpoint power_trace_threshold_shift_down_stable
    (threshold drift : nat)
    (xs : PowerTrace)
    : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      threshold_shift_down_stable_sample threshold drift x /\
      power_trace_threshold_shift_down_stable threshold drift xs'
  end.

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

Lemma window_above_threshold_upward_drift_invariant :
  forall drift threshold sample,
    threshold_shift_up_stable_sample threshold drift sample ->
    window_above_threshold (threshold + drift) sample =
      window_above_threshold threshold sample.
Proof.
  intros drift threshold sample Hstable.
  unfold window_above_threshold.
  destruct (Nat.leb (threshold + drift) sample) eqn:Hup;
    destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
  - apply Nat.leb_le in Hup.
    apply Nat.leb_gt in Hbase.
    lia.
  - destruct Hstable as [Hbelow | Habove].
    + apply Nat.leb_gt in Hup.
      apply Nat.leb_le in Hbase.
      lia.
    + apply Nat.leb_gt in Hup.
      apply Nat.leb_le in Hbase.
      lia.
Qed.

Theorem threshold_trace_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    threshold_trace (threshold + drift) xs =
      threshold_trace threshold xs.
Proof.
  intros drift threshold xs Hstable.
  induction xs as [|x xs IH]; simpl in *.
  - reflexivity.
  - destruct Hstable as [Hx Hxs].
    rewrite window_above_threshold_upward_drift_invariant by exact Hx.
    rewrite IH by exact Hxs.
    reflexivity.
Qed.

Lemma window_above_threshold_downward_drift_invariant :
  forall drift threshold sample,
    drift <= threshold ->
    threshold_shift_down_stable_sample threshold drift sample ->
    window_above_threshold (threshold - drift) sample =
      window_above_threshold threshold sample.
Proof.
  intros drift threshold sample Hdrift Hstable.
  unfold window_above_threshold.
  destruct Hstable as [Hbelow | Habove].
  - destruct (Nat.leb (threshold - drift) sample) eqn:Hdown;
      destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
    + apply Nat.leb_le in Hdown.
      apply Nat.leb_gt in Hbase.
      lia.
    + apply Nat.leb_gt in Hdown.
      apply Nat.leb_le in Hbase.
      lia.
  - destruct (Nat.leb (threshold - drift) sample) eqn:Hdown;
      destruct (Nat.leb threshold sample) eqn:Hbase; try reflexivity.
    + apply Nat.leb_le in Hdown.
      apply Nat.leb_gt in Hbase.
      lia.
    + apply Nat.leb_gt in Hdown.
      apply Nat.leb_le in Hbase.
      lia.
Qed.

Theorem threshold_trace_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    threshold_trace (threshold - drift) xs =
      threshold_trace threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  induction xs as [|x xs IH]; simpl in *.
  - reflexivity.
  - destruct Hstable as [Hx Hxs].
    rewrite window_above_threshold_downward_drift_invariant
      by exact Hdrift || exact Hx.
    rewrite IH by exact Hdrift || exact Hxs.
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

Theorem canonical_packet24_byte_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_byte_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_nibble_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_scale_invariant :
  forall factor threshold xs,
    0 < factor ->
    canonical_packet24_field_view_from_powers (factor * threshold) (scale_powers factor xs) =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros factor threshold xs Hfactor.
  unfold canonical_packet24_field_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_scale_invariant :
  forall spec factor threshold xs,
    0 < factor ->
    canonical_packet_structure_view_from_powers spec (factor * threshold) (scale_powers factor xs) =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec factor threshold xs Hfactor.
  unfold canonical_packet_structure_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_scale_invariant
             factor threshold xs Hfactor).
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_scale_invariant :
  forall schema factor threshold xs,
    0 < factor ->
    canonical_field_counter_view_from_powers schema (factor * threshold) (scale_powers factor xs) =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema factor threshold xs Hfactor.
  unfold canonical_field_counter_view_from_powers.
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

Theorem canonical_packet24_byte_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_byte_view_from_powers threshold ys =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_nibble_view_from_powers threshold ys =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_margin_invariant :
  forall threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet24_field_view_from_powers threshold ys =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet24_field_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_margin_invariant :
  forall spec threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_packet_structure_view_from_powers spec threshold ys =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec threshold margin xs ys Hmargin Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite (canonical_frame_bits_from_powers_margin_invariant
             threshold margin xs ys Hmargin Hstable).
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_margin_invariant :
  forall schema threshold margin xs ys,
    power_trace_within_margin margin xs ys ->
    power_trace_threshold_stable threshold margin xs ->
    canonical_field_counter_view_from_powers schema threshold ys =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema threshold margin xs ys Hmargin Hstable.
  unfold canonical_field_counter_view_from_powers.
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

Theorem canonical_packet24_byte_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_byte_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_byte_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_byte_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet24_nibble_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_nibble_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_nibble_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_nibble_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet24_field_view_from_powers_offset_invariant :
  forall offset threshold xs,
    canonical_packet24_field_view_from_powers (offset + threshold) (offset_powers offset xs) =
      canonical_packet24_field_view_from_powers threshold xs.
Proof.
  intros offset threshold xs.
  unfold canonical_packet24_field_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_offset_invariant :
  forall spec offset threshold xs,
    canonical_packet_structure_view_from_powers spec (offset + threshold) (offset_powers offset xs) =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec offset threshold xs.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_offset_invariant :
  forall schema offset threshold xs,
    canonical_field_counter_view_from_powers schema (offset + threshold) (offset_powers offset xs) =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema offset threshold xs.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_offset_invariant.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_frame_bits_from_powers (threshold + drift) xs =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes,
    canonical_pulse_classes_from_powers, pulse_runs_from_powers.
  rewrite threshold_trace_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_frame_word_from_powers (threshold + drift) xs =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_upward_drift_invariant :
  forall drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_packet24_from_powers (threshold + drift) xs =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros drift threshold xs Hstable.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_upward_drift_invariant :
  forall spec drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_packet_structure_view_from_powers spec (threshold + drift) xs =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec drift threshold xs Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_upward_drift_invariant :
  forall schema drift threshold xs,
    power_trace_threshold_shift_up_stable threshold drift xs ->
    canonical_field_counter_view_from_powers schema (threshold + drift) xs =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema drift threshold xs Hstable.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_upward_drift_invariant by exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_bits_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_frame_bits_from_powers (threshold - drift) xs =
      canonical_frame_bits_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_frame_bits_from_powers, frame_bits_from_classes,
    canonical_pulse_classes_from_powers, pulse_runs_from_powers.
  rewrite threshold_trace_downward_drift_invariant by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_frame_word_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_frame_word_from_powers (threshold - drift) xs =
      canonical_frame_word_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_frame_word_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet24_from_powers_downward_drift_invariant :
  forall drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_packet24_from_powers (threshold - drift) xs =
      canonical_packet24_from_powers threshold xs.
Proof.
  intros drift threshold xs Hdrift Hstable.
  unfold canonical_packet24_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_packet_structure_view_from_powers_downward_drift_invariant :
  forall spec drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_packet_structure_view_from_powers spec (threshold - drift) xs =
      canonical_packet_structure_view_from_powers spec threshold xs.
Proof.
  intros spec drift threshold xs Hdrift Hstable.
  unfold canonical_packet_structure_view_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
  reflexivity.
Qed.

Theorem canonical_field_counter_view_from_powers_downward_drift_invariant :
  forall schema drift threshold xs,
    drift <= threshold ->
    power_trace_threshold_shift_down_stable threshold drift xs ->
    canonical_field_counter_view_from_powers schema (threshold - drift) xs =
      canonical_field_counter_view_from_powers schema threshold xs.
Proof.
  intros schema drift threshold xs Hdrift Hstable.
  unfold canonical_field_counter_view_from_powers.
  rewrite canonical_frame_bits_from_powers_downward_drift_invariant
    by exact Hdrift || exact Hstable.
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

Definition canonical_packet24_byte_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24ByteView :=
  packet24_byte_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_nibble_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24NibbleView :=
  packet24_nibble_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet24_field_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : Packet24FieldView :=
  packet24_field_view_from_bits (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_packet_structure_view_from_iq
    (spec : PacketStructureSpec)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : list PacketStructuredFieldValue :=
  packet_structure_view_from_bits spec
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_field_counter_view_from_iq
    (schema : CounterSchema)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  field_counter_view_from_bits schema (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition canonical_hi16_lo8_counter_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  canonical_field_counter_view_from_iq hi16_lo8_counter_schema window_pairs threshold xs.

Definition canonical_prefix12_suffix12_counter_view_from_iq
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : FieldCounterView :=
  canonical_field_counter_view_from_iq prefix12_suffix12_counter_schema window_pairs threshold xs.

Definition canonical_field_counter_fresh_from_iq
    (schema : CounterSchema)
    (state : FieldCounterState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : bool :=
  field_counter_fresh state
    (canonical_field_counter_view_from_iq schema window_pairs threshold xs).

Definition canonical_packet_schema_fresh_from_iq
    (kind : PacketSchemaKind)
    (state : PacketSchemaState)
    (window_pairs threshold : nat)
    (xs : ByteStream)
    : bool :=
  packet_schema_fresh_from_bits kind state
    (canonical_frame_bits_from_iq window_pairs threshold xs).

Definition iq_window_energy_equivalent
    (window_pairs : nat)
    (xs ys : ByteStream)
    : Prop :=
  iq_window_energy_trace window_pairs xs =
    iq_window_energy_trace window_pairs ys.

Theorem iq_window_energy_equivalent_implies_pulse_runs_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    pulse_runs_from_iq window_pairs threshold xs =
      pulse_runs_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold iq_window_energy_equivalent, pulse_runs_from_iq in *.
  rewrite Heq.
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_frame_bits_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_frame_bits_from_iq window_pairs threshold xs =
      canonical_frame_bits_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold canonical_frame_bits_from_iq, canonical_pulse_classes_from_iq.
  rewrite (iq_window_energy_equivalent_implies_pulse_runs_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_frame_word_invariant :
  forall window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_frame_word_from_iq window_pairs threshold xs =
      canonical_frame_word_from_iq window_pairs threshold ys.
Proof.
  intros window_pairs threshold xs ys Heq.
  unfold canonical_frame_word_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_packet_structure_invariant :
  forall spec window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_packet_structure_view_from_iq spec window_pairs threshold xs =
      canonical_packet_structure_view_from_iq spec window_pairs threshold ys.
Proof.
  intros spec window_pairs threshold xs ys Heq.
  unfold canonical_packet_structure_view_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Theorem iq_window_energy_equivalent_implies_counter_view_invariant :
  forall schema window_pairs threshold xs ys,
    iq_window_energy_equivalent window_pairs xs ys ->
    canonical_field_counter_view_from_iq schema window_pairs threshold xs =
      canonical_field_counter_view_from_iq schema window_pairs threshold ys.
Proof.
  intros schema window_pairs threshold xs ys Heq.
  unfold canonical_field_counter_view_from_iq.
  rewrite (iq_window_energy_equivalent_implies_frame_bits_invariant
             window_pairs threshold xs ys Heq).
  reflexivity.
Qed.

Definition frame_bits_sequence_from_iq
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : list (list bool) :=
  map (canonical_frame_bits_from_iq window_pairs threshold) xss.

Definition counter_schema_fits_iqb
    (schema : CounterSchema)
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : bool :=
  counter_schema_fits_bitsb schema
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition counter_schema_fit_report_from_iq_sequence
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : CounterSchemaFitReport :=
  counter_schema_fit_report_from_bits
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition counter_schema_classification_code_from_iq_sequence
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : nat :=
  counter_schema_classification_code_from_bits
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Definition prefix12_stronger_than_hi16_lo8_from_iqb
    (window_pairs threshold : nat)
    (xss : list ByteStream)
    : bool :=
  prefix12_stronger_than_hi16_lo8b
    (frame_bits_sequence_from_iq window_pairs threshold xss).

Theorem counter_schema_fits_iqb_sound :
  forall schema window_pairs threshold xss,
    counter_schema_fits_iqb schema window_pairs threshold xss = true ->
    counter_schema_fits_bits schema
      (frame_bits_sequence_from_iq window_pairs threshold xss).
Proof.
  intros schema window_pairs threshold xss Hfit.
  unfold counter_schema_fits_iqb.
  apply counter_schema_fits_bitsb_sound.
  exact Hfit.
Qed.

Theorem counter_schema_classification_code_from_iq_sequence_singleton :
  forall window_pairs threshold xs,
    counter_schema_classification_code_from_iq_sequence window_pairs threshold [xs] = 3.
Proof.
  intros window_pairs threshold xs.
  unfold counter_schema_classification_code_from_iq_sequence,
    counter_schema_classification_code_from_bits,
    counter_schema_fit_report_from_bits,
    frame_bits_sequence_from_iq.
  simpl.
  reflexivity.
Qed.

Theorem prefix12_stronger_than_hi16_lo8_from_iqb_sound :
  forall window_pairs threshold xss,
    prefix12_stronger_than_hi16_lo8_from_iqb window_pairs threshold xss = true ->
    counter_schema_fits_bitsb hi16_lo8_counter_schema
      (frame_bits_sequence_from_iq window_pairs threshold xss) = false /\
    counter_schema_fits_bits prefix12_suffix12_counter_schema
      (frame_bits_sequence_from_iq window_pairs threshold xss).
Proof.
  intros window_pairs threshold xss Hstrong.
  unfold prefix12_stronger_than_hi16_lo8_from_iqb in Hstrong.
  apply prefix12_stronger_than_hi16_lo8b_sound.
  exact Hstrong.
Qed.

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
     tower_packet24 := canonical_packet24_from_iq window_pairs threshold xs;
     tower_fields := canonical_packet24_field_view_from_iq window_pairs threshold xs |}.

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

Theorem observed_iq_matches_family_implies_field_view :
  forall base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet24_field_view_from_iq window_pairs threshold xs =
      canonical_packet24_field_view_from_runs base_pattern.
Proof.
  intros base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet24_field_view_from_iq, canonical_packet24_field_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_packet_structure :
  forall spec base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_packet_structure_view_from_iq spec window_pairs threshold xs =
      canonical_packet_structure_view_from_runs spec base_pattern.
Proof.
  intros spec base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_packet_structure_view_from_iq,
    canonical_packet_structure_view_from_runs.
  rewrite (observed_iq_matches_family_implies_frame_bits
             base_pattern window_pairs threshold xs Hmatch).
  reflexivity.
Qed.

Theorem observed_iq_matches_family_implies_counter_view :
  forall schema base_pattern window_pairs threshold xs,
    observed_iq_matches_family base_pattern window_pairs threshold xs ->
    canonical_field_counter_view_from_iq schema window_pairs threshold xs =
      canonical_field_counter_view_from_runs schema base_pattern.
Proof.
  intros schema base_pattern window_pairs threshold xs Hmatch.
  unfold canonical_field_counter_view_from_iq, canonical_field_counter_view_from_runs.
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
  rewrite (observed_iq_matches_family_implies_field_view
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

Theorem frame_bits_invariant_between_iq_regimes_implies_field_view_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_field_view_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_field_view_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet24_field_view_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_packet_structure_invariant :
  forall spec window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_structure_view_from_iq spec window_pairs1 threshold1 xs =
      canonical_packet_structure_view_from_iq spec window_pairs2 threshold2 xs.
Proof.
  intros spec window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_packet_structure_view_from_iq.
  rewrite Hbits.
  reflexivity.
Qed.

Theorem frame_bits_invariant_between_iq_regimes_implies_counter_view_invariant :
  forall schema window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_frame_bits_from_iq window_pairs1 threshold1 xs =
      canonical_frame_bits_from_iq window_pairs2 threshold2 xs ->
    canonical_field_counter_view_from_iq schema window_pairs1 threshold1 xs =
      canonical_field_counter_view_from_iq schema window_pairs2 threshold2 xs.
Proof.
  intros schema window_pairs1 threshold1 window_pairs2 threshold2 xs Hbits.
  unfold canonical_field_counter_view_from_iq.
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

Theorem class_invariant_between_iq_regimes_implies_field_view_invariant :
  forall window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet24_field_view_from_iq window_pairs1 threshold1 xs =
      canonical_packet24_field_view_from_iq window_pairs2 threshold2 xs.
Proof.
  intros window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet24_field_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_packet_structure_invariant :
  forall spec window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_packet_structure_view_from_iq spec window_pairs1 threshold1 xs =
      canonical_packet_structure_view_from_iq spec window_pairs2 threshold2 xs.
Proof.
  intros spec window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_packet_structure_view_from_iq.
  rewrite (class_invariant_between_iq_regimes_implies_frame_bits_invariant
             window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses).
  reflexivity.
Qed.

Theorem class_invariant_between_iq_regimes_implies_counter_view_invariant :
  forall schema window_pairs1 threshold1 window_pairs2 threshold2 xs,
    canonical_pulse_classes_from_iq window_pairs1 threshold1 xs =
      canonical_pulse_classes_from_iq window_pairs2 threshold2 xs ->
    canonical_field_counter_view_from_iq schema window_pairs1 threshold1 xs =
      canonical_field_counter_view_from_iq schema window_pairs2 threshold2 xs.
Proof.
  intros schema window_pairs1 threshold1 window_pairs2 threshold2 xs Hclasses.
  unfold canonical_field_counter_view_from_iq.
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
  rewrite (class_invariant_between_iq_regimes_implies_field_view_invariant
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

