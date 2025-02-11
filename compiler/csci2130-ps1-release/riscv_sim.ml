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
let rec interp (init_state : state) : state = init_state

(* let load2word (pc: int32) (m: memory) : int32 = 
  read_word_little_endian (m pc) *)

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
    (* | 0b0010011l -> Ori *)
    | 0b0000011l -> Lw (rd, rs1, imm_i) (*I*)
    | 0b0100011l -> Sw (rs1, rs2, imm_s) (*S*)
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
