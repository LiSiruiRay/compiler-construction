open Riscv_ast
open Riscv_assem
open Byte

exception TODO
exception FatalError


(* Take a look at the definition of the RISC-V AST and machine state in mips_ast.ml *)

(* Given a starting state, simulate the RISC-V machine code to get a final state;
   a final state is reached if the the next instruction pointed to by the PC is
   all 0s.
 *)
 let load2word (pc: int32) (m: memory) : int32 = 
  read_word_little_endian m pc



(* let opcode2inst (curOpcode: int32): (reg * reg * reg) -> inst =
  match curOpcode with
    | 0b0110011l -> Add
    | 0b0010011l -> Addi
    | 0b1100011l -> Beq
    | 0b1101111l -> Jal
    | 0b1100111l -> Jalr
    | 0b0110111l -> Lui
    | 0b0010011l -> Ori
    | 0b0000011l -> Lw
    | 0b0100011l -> Sw
    | _ -> Li *)
let word2inst (w: int32) : inst = 
  let curOpcode = bitrange w 0 6 in
  let rd = ind2reg (bitrange w 7 11) in
  let rs1 = ind2reg (bitrange w 15 19) in
  let rs2 = ind2reg (bitrange w 20 24) in
  let imm_u = combine_bits[(bitrange w 12 31, 20)] in
  let imm_i = (bitrange w 0 11) in
  let imm_j = combine_bits[(bitrange w 21 30, 10);(bitrange w 20 20, 1);(bitrange w 12 19, 8);(bitrange w 31 31,1)] in
  let imm_s = combine_bits[(bitrange w 7 11, 4);(bitrange w 25 31, 7)] in
  let offset_b = combine_bits[(bitrange w 8 11, 4);(bitrange w 25 30, 6);(bitrange w 7 7, 1);(bitrange w 31 31,1)] in
    match curOpcode with
    | 0b0110011l -> Add (rd, rs1, rs2)
    | 0b0010011l -> 
      let funct3 = (bitrange w 12 14) in
      let imm = (bitrange w 15 19) in
        (match funct3 with
        | 0b110l -> Ori (rd, rs1, imm)
        | _ -> Addi (rd, rs1, imm))
    | 0b1100011l -> Beq (rs1, rs2, offset_b) (*B*)
    | 0b1101111l -> Jal (rd, imm_j) (*J*)
    | 0b1100111l -> Jalr (rd, rs1, imm_i)
    | 0b0110111l -> Lui (rd, imm_u) (*U*)
    | 0b0000011l -> Lw (rd, rs1, imm_i) (*I*)
    | 0b0100011l -> Sw (rs1, rs2, imm_s) (*S*)
    | _ -> raise FatalError;;

let step_sw (i: reg * reg * int32) (m: memory) : memory =
  let (rs1, rs2, imm_s) = i in
  let mem_addr = Int32.add (reg2ind32 rs1) imm_s in
  mem_update mem_addr ({b= (reg2ind32 rs1)}) m

    (*later*)
let step_lw (i: reg * reg * int32) (m: memory) : int32 =
  let (_, rs1, imm_i) = i in
  let mem_addr = Int32.add imm_i (reg2ind32 rs1) in
  let mem_val = mem_lookup mem_addr m in
mem_val.b

let step_lui (i: reg * int32) (m: memory) : int32 =
  let (rd, imm_u) = i in 
  let mem_addr = Int32.add (reg2ind32 rd) imm_u in
  let mem_val = mem_lookup mem_addr m in
  mem_val.b;;

(*take a register and an offset, return a new register (rd) and a new pc*)
let step_jalr (i: reg * reg * int32) (pc: int32) : int32 * int32 =
  let (rd, rs1, imm_i) = i in
  let rd_return = Int32.add pc 4l in
  let des_pc = Int32.add (reg2ind32 rs1) imm_i in
  (des_pc, rd_return);;
(*take a register and an offset, return a new register (rd) and a new pc*)
let step_jal (i: reg * int32) (pc: int32): int32 * int32 = 
  let (rd, imm_j) = i in 
  let rd_return = (Int32.add pc 4l) in
  ((Int32.add pc imm_j), rd_return);;


let step_beq (i: reg * reg * int32): int32 =
  let (rs1, rs2, offset_b) = i in 
  let rs1_int32 = reg2ind32 rs1 in
  let rs2_int32 = reg2ind32 rs2 in
  if rs1_int32 = rs2_int32 then offset_b else 4l;;

let step_add (i: reg * reg * reg) : int32 =
  let (_, rs1, rs2) = i in (*(rd, rs1, rs2)*)
  let rs1_int32 = reg2ind32 rs1 in
  let rs2_int32 = reg2ind32 rs2 in
  Int32.add rs1_int32 rs2_int32;;

  (*return register value*)
let step_ori (i: reg * reg * int32): int32 =
  let (_, rs1, imm) = i in (*(rd, rs1, imm)*)
  let rs1_int32 = reg2ind32 rs1 in
  (Int32.logor rs1_int32 imm);;

let step_addi (i: reg * reg * int32): int32 =
  let (_, rs1, imm) = i in (*(rd, rs1, imm)*)
  let rs1_int32 = reg2ind32 rs1 in
 (Int32.add rs1_int32 imm);;

  let rec interp (init_state : state) : state = 
    let _ = print_endline "start of the interp" in
    let old_reg_file = init_state.r in
    let old_pc = init_state.pc in
    let old_m = init_state.m in
    let nextw = load2word old_pc old_m in
    let _ = print_endline "nextw:" in
    let _ = print_endline (Int32.to_string nextw) in
    if nextw = Int32.zero then init_state else
      let i = word2inst nextw in
      match i with
      | Add (rd, rs1, rs2) -> 
        let new_reg_val = step_add (rd, rs1, rs2) in
        let new_reg_file = rf_update (reg2ind rd) new_reg_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=Int32.add old_pc 4l; m=old_m} in
      interp new_state
      | Ori (rd, rs1, imm) -> 
        let new_reg_val = step_ori (rd, rs1, imm) in
        let new_reg_file = rf_update (reg2ind rd) new_reg_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=Int32.add old_pc 4l; m=old_m} in
      interp new_state
      | Addi (rd, rs1, imm) ->
        let new_reg_val = step_addi (rd, rs1, imm) in
        let new_reg_file = rf_update (reg2ind rd) new_reg_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=Int32.add old_pc 4l; m=old_m} in
      interp new_state
      | Beq (rs1, rs2, offset_b) ->
        let offset = step_beq (rs1, rs2, offset_b) in
        let new_state: state = {r=old_reg_file; pc=Int32.add old_pc offset; m=old_m} in
      interp new_state
      | Jal (rd, imm_j) ->
        let (new_pc, new_rd_val) = step_jal (rd, imm_j) (old_pc) in
        let new_reg_file = rf_update (reg2ind rd) new_rd_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=new_pc; m=old_m} in
      interp new_state
      | Jalr (rd, rs1, imm_i) ->
        let (new_pc, new_rd_val) = step_jalr (rd, rs1, imm_i) (old_pc) in
        let new_reg_file = rf_update (reg2ind rd) new_rd_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=new_pc; m=old_m} in
      interp new_state
      | Lui (rd, imm_u) ->
        let new_rd_val = step_lui (rd, imm_u) (old_m) in
        let new_reg_file = rf_update (reg2ind rd) new_rd_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=Int32.add old_pc 4l; m=old_m} in
      interp new_state
      | Lw (rd, rs1, imm_i) ->
        let new_rd_val = step_lw (rd, rs1, imm_i) (old_m) in
        let new_reg_file = rf_update (reg2ind rd) new_rd_val old_reg_file in
        let new_state: state = {r=new_reg_file; pc=Int32.add old_pc 4l; m=old_m} in
      interp new_state
      | Sw (rs1, rs2, imm_s) ->
        let new_m = step_sw (rs1, rs2, imm_s) (old_m) in
        let new_state: state = {r=old_reg_file; pc=Int32.add old_pc 4l; m=new_m} in
      interp new_state
      | _ -> raise FatalError


(*
  Here are a few details/assumptions about the assembler and interpreter that the autograder makes:
  * > Little Endian Encoding
  * > Program Data is stored starting at 0x400000
  * > Constants that occur as input to the assembler are passed directly as 32bit immediates in the AST,
      without any shifting or masking. The assembler then takes subsets of these bits when actually encoding
      an instruction into memory. E.g. an addi can be passed an immediate that 15 bits, but when we encode
      that instruction the encoding only uses bits 0 through 11.
*)
