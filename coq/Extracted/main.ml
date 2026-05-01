(* coq/Extracted/main.ml — driver for the extracted Coq xmss_chain_step.

   Takes 5 args: x, pub_seed (each as 64-char hex / 32 bytes), and
   key_idx, chain_idx, step (decimal ints). Calls the extracted
   xmss_chain_step and prints the result as 64-char hex.

   Extraction with the placeholder hash + pack_adrs (see
   coq/Tzel/Extraction.v) makes this driver always print a zero
   felt — the point of this first commit is exercising the
   build/extract/run pipeline end-to-end, not producing meaningful
   chain hashes. The next commit wires Hash3 and pack_adrs_chain to
   the bit-equivalent OCaml protocol port and adds a differential
   check against the Cairo [xmss_chain_step]. *)

let parse_hex_felt s =
  if String.length s <> 64 then begin
    Printf.eprintf "expected 64-char hex felt, got %d chars\n" (String.length s);
    exit 2
  end;
  let bytes = Bytes.create 32 in
  for i = 0 to 31 do
    let nybble c =
      match c with
      | '0'..'9' -> Char.code c - Char.code '0'
      | 'a'..'f' -> Char.code c - Char.code 'a' + 10
      | 'A'..'F' -> Char.code c - Char.code 'A' + 10
      | _ ->
        Printf.eprintf "bad hex char %C\n" c;
        exit 2
    in
    let hi = nybble s.[2 * i] in
    let lo = nybble s.[2 * i + 1] in
    Bytes.set_uint8 bytes i ((hi lsl 4) lor lo)
  done;
  bytes

let print_hex_felt b =
  let buf = Buffer.create 64 in
  for i = 0 to 31 do
    Buffer.add_string buf (Printf.sprintf "%02x" (Bytes.get_uint8 b i))
  done;
  print_string (Buffer.contents buf);
  print_newline ()

let () =
  let argv = Sys.argv in
  if Array.length argv <> 6 then begin
    prerr_endline
      "usage: main <x_hex64> <pub_seed_hex64> <key_idx> <chain_idx> <step>";
    exit 2
  end;
  let x = parse_hex_felt argv.(1) in
  let pub_seed = parse_hex_felt argv.(2) in
  let key_idx = int_of_string argv.(3) in
  let chain_idx = int_of_string argv.(4) in
  let step = int_of_string argv.(5) in
  let result =
    Tzel_wots.xmss_chain_step x pub_seed key_idx chain_idx step
  in
  print_hex_felt result
