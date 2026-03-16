open Printf
open Burst_detector_extracted

type config = {
  crop_window_pairs : int option;
  crop_threshold : int option;
  crop_pad_windows : int;
}

let default_config = {
  crop_window_pairs = None;
  crop_threshold = None;
  crop_pad_windows = 8;
}

let read_file_bytes path =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let data = really_input_string ic len in
  close_in ic;
  let rec loop i acc =
    if i < 0 then acc else loop (i - 1) (Char.code data.[i] :: acc)
  in
  loop (len - 1) []

let string_of_bool b = if b then "true" else "false"

let string_of_bool_list xs =
  "[" ^ String.concat "," (List.map string_of_bool xs) ^ "]"

let string_of_boundary_kind = function
  | BoundaryStable -> "stable"
  | BoundaryMetamer -> "metamer"
  | BoundaryTruncation -> "truncation"
  | BoundaryDrift -> "drift"

let string_of_boundary_kind_list xs =
  "[" ^ String.concat "," (List.map string_of_boundary_kind xs) ^ "]"

let string_of_pulse_class = function
  | MarkShort -> "MS"
  | MarkLong -> "ML"
  | GapShort -> "GS"
  | GapLong -> "GL"
  | GapBreak -> "GB"

let string_of_role = function
  | PacketFieldPrefix -> "prefix"
  | PacketFieldPayload -> "payload"
  | PacketFieldCounter -> "counter"
  | PacketFieldFlag -> "flag"
  | PacketFieldCheck -> "check"
  | PacketFieldBoundary -> "boundary"
  | PacketFieldReserved -> "reserved"

let string_of_structured_field field =
  sprintf "%s@%d/%d=%d"
    (string_of_role field.structured_field_role)
    field.structured_field_offset
    field.structured_field_width
    field.structured_field_value

let string_of_structure fields =
  "[" ^ String.concat ";"
    (List.map string_of_structured_field fields) ^ "]"

let string_of_regime regime =
  sprintf "%d:%d"
    regime.regime_window_pairs
    regime.regime_threshold

let string_of_regime_list rs =
  "[" ^ String.concat "," (List.map string_of_regime rs) ^ "]"

let option_or default = function
  | Some x -> x
  | None -> default

let min_regime_window_pairs = function
  | [] -> 20
  | r :: rs ->
      List.fold_left
        (fun acc regime -> min acc regime.regime_window_pairs)
        r.regime_window_pairs rs

let min_regime_threshold = function
  | [] -> 131072
  | r :: rs ->
      List.fold_left
        (fun acc regime -> min acc regime.regime_threshold)
        r.regime_threshold rs

let crop_window_span_bytes window_pairs =
  max 2 (2 * window_pairs)

let list_take n xs =
  let rec loop k acc = function
    | [] -> List.rev acc
    | _ when k <= 0 -> List.rev acc
    | x :: rest -> loop (k - 1) (x :: acc) rest
  in
  loop n [] xs

let rec list_drop n xs =
  if n <= 0 then xs else
  match xs with
  | [] -> []
  | _ :: rest -> list_drop (n - 1) rest

let list_slice start len xs =
  list_take len (list_drop start xs)

let active_crop_bounds crop_window_pairs crop_threshold pad_windows bytes =
  match
    first_active_iq_window crop_window_pairs crop_threshold bytes,
    last_active_iq_window crop_window_pairs crop_threshold bytes
  with
  | Some first_idx, Some last_idx ->
      let span_bytes = crop_window_span_bytes crop_window_pairs in
      let stop_idx = last_idx + pad_windows + 1 in
      let start_byte = 0 in
      let stop_byte = min (List.length bytes) (stop_idx * span_bytes) in
      if stop_byte > start_byte then Some (start_byte, stop_byte) else None
  | _ -> None

let crop_bytes_for_regimes config regimes bytes =
  let crop_window_pairs =
    option_or (min_regime_window_pairs regimes) config.crop_window_pairs in
  let crop_threshold =
    option_or (min_regime_threshold regimes) config.crop_threshold in
  match
    active_crop_bounds
      crop_window_pairs crop_threshold config.crop_pad_windows bytes
  with
  | Some (start_byte, stop_byte) ->
      let cropped = list_slice start_byte (stop_byte - start_byte) bytes in
      (crop_window_pairs, crop_threshold, Some (start_byte, stop_byte, cropped))
  | None ->
      (crop_window_pairs, crop_threshold, None)

let descriptor_of_name = function
  | "static" -> static_packet24_schema_descriptor
  | "prefix12_suffix12" -> prefix12_suffix12_counter_schema_descriptor
  | "prefix20_lo4" -> prefix20_lo4_counter_schema_descriptor
  | "prefix16_check4_counter4" -> prefix16_check4_counter4_schema_descriptor
  | "prefix16_boundary4_counter4" -> prefix16_boundary4_counter4_schema_descriptor
  | "prefix8_flag4_payload8_counter4" ->
      prefix8_flag4_payload8_counter4_schema_descriptor
  | "prefix12_check4_payload4_counter4" ->
      prefix12_check4_payload4_counter4_schema_descriptor
  | "prefix12_check4_boundary4_counter4" ->
      prefix12_check4_boundary4_counter4_schema_descriptor
  | "prefix12_flag4_payload4_counter4" ->
      prefix12_flag4_payload4_counter4_schema_descriptor
  | "prefix12_flag4_boundary4_counter4" ->
      prefix12_flag4_boundary4_counter4_schema_descriptor
  | "prefix8_check4_flag4_payload4_counter4" ->
      prefix8_check4_flag4_payload4_counter4_schema_descriptor
  | "prefix8_check4_flag4_boundary4_counter4" ->
      prefix8_check4_flag4_boundary4_counter4_schema_descriptor
  | "prefix8_flag4_check4_payload4_counter4" ->
      prefix8_flag4_check4_payload4_counter4_schema_descriptor
  | "prefix8_flag4_check4_boundary4_counter4" ->
      prefix8_flag4_check4_boundary4_counter4_schema_descriptor
  | name -> failwith ("unknown descriptor: " ^ name)

let parse_regime spec =
  match String.split_on_char ':' spec with
  | [wp; th] ->
      { regime_window_pairs = int_of_string wp;
        regime_threshold = int_of_string th }
  | _ -> failwith ("bad regime spec: " ^ spec ^ " (expected wp:threshold)")

let hex_of_frame_bits bits =
  let width = max 1 ((List.length bits + 3) / 4) in
  sprintf "%0*x" width (bits_to_nat bits)

let class_digest classes =
  let payload = String.concat "," (List.map string_of_pulse_class classes) in
  Digest.to_hex (Digest.string payload)

let phase_signature_for_regime descriptor bytes regime =
  packet_schema_descriptor_phase_signature_from_iq
    descriptor
    empty_packet_schema_state
    regime.regime_window_pairs
    regime.regime_threshold
    bytes

let rec adjacent_bool_flags f = function
  | [] -> []
  | [_] -> []
  | x :: ((y :: _) as rest) -> f x y :: adjacent_bool_flags f rest

let phase_path_from_bytes label descriptor bytes regimes =
  let signatures =
    List.map (phase_signature_for_regime descriptor bytes) regimes in
  let class_mask =
    adjacent_bool_flags
      (fun s1 s2 ->
         not (pulse_class_list_eqb
                s1.phase_signature_object
                s2.phase_signature_object))
      signatures in
  let phase_mask =
    adjacent_bool_flags
      (fun s1 s2 ->
         not (packet_schema_descriptor_phase_signature_eqb s1 s2))
      signatures in
  let boundary_mask =
    observation_regime_boundary_kind_mask bytes regimes in
  let path_class_stable = not (List.exists (fun b -> b) class_mask) in
  let path_phase_stable = not (List.exists (fun b -> b) phase_mask) in
  printf "FILE=%s\n" label;
  printf "SIZE=%d\n" (List.length bytes);
  printf "REGIMES=%s\n" (string_of_regime_list regimes);
  printf "PATH_CLASS_STABLE=%s\n" (string_of_bool path_class_stable);
  printf "PATH_PHASE_STABLE=%s\n" (string_of_bool path_phase_stable);
  printf "CLASS_TRANSITIONS=%s\n" (string_of_bool_list class_mask);
  printf "PHASE_TRANSITIONS=%s\n" (string_of_bool_list phase_mask);
  printf "BOUNDARY_KINDS=%s\n" (string_of_boundary_kind_list boundary_mask);
  List.iteri
    (fun i regime ->
       let sigi = List.nth signatures i in
       printf "REGIME_%d=%s\n" i (string_of_regime regime);
       printf "BASE_%d=%d\n" i
         (canonical_pulse_base_from_iq
            regime.regime_window_pairs
            regime.regime_threshold
            bytes);
       printf "CLASS_DIGEST_%d=%s\n" i
         (class_digest sigi.phase_signature_object);
       printf "FRAME_BITS_LEN_%d=%d\n" i
         sigi.phase_signature_frame_bit_count;
       printf "FRAME_HEX_%d=%s\n" i
         (hex_of_frame_bits sigi.phase_signature_decoded_view.view_bits);
       printf "STRUCTURE_%d=%s\n" i
         (string_of_structure
            sigi.phase_signature_schema_observation
              .descriptor_observation_structure);
       printf "FRESH_%d=%s\n" i
         (string_of_bool
            sigi.phase_signature_schema_observation
              .descriptor_observation_fresh))
    regimes

let fast_phase_path config descriptor path regime_specs =
  let bytes = read_file_bytes path in
  let regimes = List.map parse_regime regime_specs in
  let crop_window_pairs, crop_threshold, cropped =
    crop_bytes_for_regimes config regimes bytes in
  printf "SOURCE_FILE=%s\n" path;
  printf "SOURCE_SIZE=%d\n" (List.length bytes);
  printf "CROP_WINDOW_PAIRS=%d\n" crop_window_pairs;
  printf "CROP_THRESHOLD=%d\n" crop_threshold;
  printf "CROP_PAD_WINDOWS=%d\n" config.crop_pad_windows;
  match cropped with
  | Some (start_byte, stop_byte, crop) ->
      printf "CROP_APPLIED=true\n";
      printf "CROP_START_BYTE=%d\n" start_byte;
      printf "CROP_STOP_BYTE=%d\n" stop_byte;
      phase_path_from_bytes
        (sprintf "%s#crop[%d:%d]" path start_byte stop_byte)
        descriptor crop regimes
  | None ->
      printf "CROP_APPLIED=false\n";
      phase_path_from_bytes path descriptor bytes regimes

let usage () =
  eprintf
    "usage:\n  atlas_runner [--crop-window-pairs N] [--crop-threshold N] [--crop-pad-windows N] phasepathfast <descriptor> <file> <wp:threshold> <wp:threshold> ...\n";
  exit 2

let rec parse_config config = function
  | "--crop-window-pairs" :: value :: rest ->
      parse_config
        { config with crop_window_pairs = Some (int_of_string value) } rest
  | "--crop-threshold" :: value :: rest ->
      parse_config
        { config with crop_threshold = Some (int_of_string value) } rest
  | "--crop-pad-windows" :: value :: rest ->
      parse_config
        { config with crop_pad_windows = int_of_string value } rest
  | args -> config, args

let () =
  let config, args =
    parse_config default_config (List.tl (Array.to_list Sys.argv)) in
  match args with
  | "phasepathfast" :: descriptor_name :: path :: regime_specs when regime_specs <> [] ->
      fast_phase_path config (descriptor_of_name descriptor_name) path regime_specs
  | _ -> usage ()
