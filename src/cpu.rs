use crate::opcodes;
use bitflags::bitflags;
use std::collections::HashMap;

bitflags! {
    /// # Status Register (P) https://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;
pub struct CPU {
    pub stack_pointer: u8,
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,

    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    Absolute,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            stack_pointer: STACK_RESET,
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.stack_pointer = STACK_RESET;
        self.status = CpuFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let position = self.mem_read(self.program_counter);
                let addr = position.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let position = self.mem_read(self.program_counter);
                let addr = position.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute_X => {
                let position = self.mem_read_u16(self.program_counter);
                let addr = position.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let position = self.mem_read_u16(self.program_counter);
                let addr = position.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    pub fn update_zero_and_negative_flags(&mut self, value: u8) {
        if value == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if value & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }

    pub fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    pub fn add_to_register_a(&mut self, value: u8) {
        let mut sum = self.register_a as u16 + value as u16;
        if self.status.contains(CpuFlags::CARRY) {
            sum = sum + 1;
        }

        let carry = sum > 0xff;
        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let res = sum as u8;

        if (value ^ res) & (res ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW);
        }

        self.set_register_a(res);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(((value as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    pub fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    pub fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.set_register_a(value);
    }

    pub fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a)
    }

    pub fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    pub fn asl_on_reg_a(&mut self) {
        let mut value = self.register_a;
        if value >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value << 1;
        self.set_register_a(value);
    }

    pub fn asl(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        if value >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value << 1;
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    pub fn lsr_on_reg_a(&mut self) {
        let mut value = self.register_a;
        if value & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value >> 1;
        self.set_register_a(value);
    }

    pub fn lsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        if value & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value >> 1;
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    pub fn branch(&mut self, condition: bool) {
        if condition {
            let offset = self.mem_read(self.program_counter) as i8;
            self.program_counter = self.program_counter.wrapping_add(1);
            let new_addr = self.program_counter.wrapping_add(offset as u16);
            self.program_counter = new_addr;
        }
    }

    pub fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        if value & self.register_a == 0{
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        self.status.set(CpuFlags::NEGATIV, value & 0b1000_0000 > 0);
        self.status.set(CpuFlags::OVERFLOW, value & 0b0100_0000 > 0);
    }

    pub fn compare(&mut self, mode: &AddressingMode, compare_with: u8) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        if value <= compare_with {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(compare_with.wrapping_sub(value));
    }

    pub fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr).wrapping_sub(1);
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    pub fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    pub fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a ^ value);
    }

    pub fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr).wrapping_add(1);
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    pub fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a | value);
    }

    pub fn push_onto_stack(&mut self, value: u8) {
        self.mem_write(STACK as u16 + self.stack_pointer as u16, value);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    pub fn php(&mut self) {
        self.push_onto_stack(self.status.bits() | 0b0011_0000);
    }

    pub fn pop_from_stack(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(STACK as u16 + self.stack_pointer as u16)
    }

    pub fn pla(&mut self) {
        let value = self.pop_from_stack();
        self.set_register_a(value)
    }

    pub fn plp(&mut self) {
        let value = self.pop_from_stack();
        self.status.bits = value;
        // FIXME
        //      not sure if PLP should be removing these two flags or not?!?
        //      https://wiki.nesdev.com/w/index.php/Status_flags#The_B_flag
        self.status.remove(CpuFlags::BREAK);
        self.status.remove(CpuFlags::BREAK2);
    }

    pub fn rol_on_reg_a(&mut self) {
        let mut value = self.register_a;
        let carry = self.status.contains(CpuFlags::CARRY);
        if value >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value << 1;
        if carry {
            value = value | 1;
        }
        self.set_register_a(value);
    }
    pub fn rol(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        let carry = self.status.contains(CpuFlags::CARRY);
        if value >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value << 1;
        if carry {
            value = value | 1;
        }
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    pub fn ror_on_reg_a(&mut self) {
        let mut value = self.register_a;
        let carry = self.status.contains(CpuFlags::CARRY);
        if value & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value >> 1;
        if carry {
            value = value | 0b1000_0000;
        }
        self.set_register_a(value);
    }

    pub fn ror(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        let carry = self.status.contains(CpuFlags::CARRY);
        if value & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        value = value >> 1;
        if carry {
            value = value | 0b1000_0000;
        }
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }


    pub fn pop_from_stack_u16(&mut self) -> u16 {
        let lo = self.pop_from_stack() as u16;
        let hi = self.pop_from_stack() as u16;
        (hi << 8) | lo
    }

    pub fn push_onto_stack_u16(&mut self, value: u16) {
        let hi = (value >> 8) as u8;
        let lo = (value & 0xff) as u8;
        self.push_onto_stack(hi);
        self.push_onto_stack(lo);
    }

    pub fn rti(&mut self) {
        self.status.bits = self.pop_from_stack();
        self.status.remove(CpuFlags::BREAK);
        self.status.remove(CpuFlags::BREAK2);
        self.program_counter = self.pop_from_stack_u16();
    }

    pub fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x)
    }

    pub fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y)
    }

    pub fn tsx(&mut self) {
        self.register_x = self.stack_pointer;
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a & value);
    }

    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;

            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode 0x{:02x} is not recognized!", code));

            match code {
                // ADC
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }

                // AND
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                // ASL
                0x0a => self.asl_on_reg_a(),

                // ASL
                0x07 | 0x16 | 0x0e | 0x1e => {
                    self.asl(&opcode.mode);
                }

                // BCC
                0x90 => self.branch(!self.status.contains(CpuFlags::CARRY)),

                // BCS
                0xb0 => self.branch(self.status.contains(CpuFlags::CARRY)),

                // BEQ
                0xf0 => self.branch(self.status.contains(CpuFlags::ZERO)),

                // BIT
                0x24 | 0x2c => {
                    self.bit(&opcode.mode)
                }

                // BMI
                0x30 => self.branch(self.status.contains(CpuFlags::NEGATIV)),

                // BNE
                0xd0 => self.branch(!self.status.contains(CpuFlags::ZERO)),

                // BPL
                0x10 => self.branch(!self.status.contains(CpuFlags::NEGATIV)),

                // BRK
                0x00 => return,

                // BVC
                0x50 => self.branch(!self.status.contains(CpuFlags::OVERFLOW)),

                // BVS
                0x70 => self.branch(self.status.contains(CpuFlags::OVERFLOW)),

                // CLC
                0x18 => self.status.remove(CpuFlags::CARRY),

                // CLD
                0xd8 => self.status.remove(CpuFlags::DECIMAL_MODE),

                // CMP
                0xc9 | 0xc5 | 0xd5 | 0xcd | 0xdd | 0xd9 | 0xc1 | 0xd1 => {
                    self.compare(&opcode.mode, self.register_a);
                }

                // CPX
                0xe0 | 0xe4 | 0xec => {
                    self.compare(&opcode.mode, self.register_x);
                }

                // CPY
                0xc0 | 0xc4 | 0xcc => {
                    self.compare(&opcode.mode, self.register_y);
                }

                // DEC
                0xc6 | 0xd6 | 0xce | 0xde => {
                    self.dec(&opcode.mode);
                }

                // DEX
                0xca => self.dex(),

                // DEY
                0x88 => self.dey(),

                // EOR
                0x49 | 0x45 | 0x55 | 0x4d | 0x5d | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }

                // INC
                0xe6 | 0xf6 | 0xee | 0xfe => {
                    self.inc(&opcode.mode);
                }

                // INX
                0xe8 => self.inx(),

                // INY
                0xc8 => self.iny(),

                // JMP Absolute
                0x4c => {
                    self.program_counter = self.mem_read_u16(self.program_counter);
                }

                // JMP Indirect
                0x6c => {
                    // https://www.nesdev.org/obelisk-6502-guide/reference.html#JMP
                    // 6502 bug mode with with page boundary:
                    //      An original 6502 has does not correctly fetch the target address
                    //      if the indirect vector falls on a page boundary
                    //      (e.g. $xxFF where xx is any value from $00 to $FF).
                    //      In this case fetches the LSB from $xxFF as expected but takes the MSB
                    //      from $xx00.
                    let ptr = self.mem_read_u16(self.program_counter);

                    let indirect_ref = if ptr & 0x00FF == 0x00FF {
                        let lo = self.mem_read(ptr);
                        let hi = self.mem_read(ptr & 0xFF00);
                        (hi as u16) << 8 | (lo as u16)
                    } else {
                        self.mem_read_u16(ptr)
                    };

                    self.program_counter = indirect_ref;
                }

                // LDA
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }

                // LSR
                0x4a => self.lsr_on_reg_a(),

                // LSR
                0x46 | 0x56 | 0x4e | 0x5e => {
                    self.lsr(&opcode.mode);
                }

                // NOP
                0xea => {},

                // ORA
                0x09 | 0x05 | 0x15 | 0x0d | 0x1d | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }

                // PHA
                0x48 => self.push_onto_stack(self.register_a),

                // PHP
                0x08 => self.php(),

                // PLA
                0x68 => self.pla(),

                // PLP
                0x28 => self.plp(),

                // ROL
                0x2a => self.rol_on_reg_a(),

                // ROL
                0x26 | 0x36 | 0x2e | 0x3e => {
                    self.rol(&opcode.mode);
                }

                // ROR
                0x6a => self.ror_on_reg_a(),

                // ROR
                0x66 | 0x76 | 0x6e | 0x7e => {
                    self.ror(&opcode.mode);
                }

                // RTI
                0x40 => self.rti(),

                // RTS
                0x60 => {
                    self.program_counter = self.pop_from_stack_u16();
                    self.program_counter += 1;
                }

                // SBC
                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }

                // SEC
                0x38 => self.status.insert(CpuFlags::CARRY),

                // SED
                0xf8 => self.status.insert(CpuFlags::DECIMAL_MODE),

                // SEI
                0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE),

                // STA
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                // STX
                0x86 | 0x96 | 0x8e => {
                    self.stx(&opcode.mode);
                }

                // STY
                0x84 | 0x94 | 0x8c => {
                    self.sty(&opcode.mode);
                }

                // TAX
                0xaa => self.tax(),

                // TAY
                0xa8 => self.tay(),

                // TSX
                0xba => self.tsx(),

                // TXA
                0x8a => self.set_register_a(self.register_x),

                // TXS
                0x9a => self.stack_pointer = self.register_x,

                // TYA
                0x98 => self.set_register_a(self.register_y),

                _ => todo!(
                    "OpCode {} [0x{:02x}] realized but not implemented",
                    opcode.mnemonic,
                    opcode.code
                ),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_update_zero_and_negative_flag_when_zero() {
        let mut cpu = CPU::new();
        cpu.update_zero_and_negative_flags(0);
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_update_zero_and_negative_flag_when_7_bit_not_set() {
        let mut cpu = CPU::new();
        cpu.update_zero_and_negative_flags(0b0000_1111);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_update_zero_and_negative_flag_when_7_bit_set() {
        let mut cpu = CPU::new();
        cpu.update_zero_and_negative_flags(0b1000_1111);

        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);

        assert_eq!(cpu.register_a, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_0xaa_tax_move_reg_a_to_reg_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xd, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 13);
    }

    #[test]
    fn test_0xa8_tay_move_reg_a_to_reg_y() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xd, 0xa8, 0x00]);

        assert_eq!(cpu.register_y, 13);
    }

    #[test]
    fn test_0xe8_add_one_to_reg_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 13);
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_0xc8_add_one_to_reg_y() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc, 0xa8, 0xc8, 0x00]);

        assert_eq!(cpu.register_y, 13);
    }

    #[test]
    fn test_iny_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xa8, 0xc8, 0xc8, 0x00]);

        assert_eq!(cpu.register_y, 1)
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_adc_with_outgoing_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0xc4, 0x00]);

        assert_eq!(cpu.register_a, 0xc3);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_adc_with_incoming_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0xc4, 0x69, 0x01, 0x00]);

        assert_eq!(cpu.register_a, 0xc5);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_sbc_without_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0xe9, 0xc4, 0x00]);

        assert_eq!(cpu.register_a, 0x3b);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
    }
    #[test]
    fn test_sbc_with_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xe9, 0xc4, 0x00]);

        assert_eq!(cpu.register_a, 0x3a);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_asl_on_register_a() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x04, 0x0a, 0x00]);

        assert_eq!(cpu.register_a, 0x08);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_asl_on_register_a_with_result_carry_set() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x0a, 0x00]);

        assert_eq!(cpu.register_a, 0xfe);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_bit_with_zero_result() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xff, 0);
        cpu.load_and_run(vec![0xa9, 0x0, 0x24, 0xff, 0x00]);

        assert!(cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_bit_with_non_zero_result() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xff, 0x01);
        cpu.load_and_run(vec![0xa9, 0x01, 0x24, 0xff, 0x00]);

        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_bit_with_negativ_flag_and_overflow_flag() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xff, 0b1100_0000);
        cpu.load_and_run(vec![0xa9, 0b1100_0000, 0x24, 0xff, 0x00]);

        assert!(cpu.status.contains(CpuFlags::NEGATIV));
        assert!(cpu.status.contains(CpuFlags::OVERFLOW));
    }

    #[test]
    fn test_dec_zero_page() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x01);
        cpu.load_and_run(vec![0xc6, 0x10, 0x00]);

        assert_eq!(cpu.mem_read(0x10), 0x00);
    }

    #[test]
    fn test_dex() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x01, 0xaa, 0xca, 0x00]);

        assert_eq!(cpu.register_x, 0x00);
    }

    #[test]
    fn test_dey() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x01, 0xa8, 0x88, 0x00]);

        assert_eq!(cpu.register_y, 0x00);
    }

    #[test]
    fn test_eor() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1100_0000, 0x49, 0b1010_1010, 0x00]);

        assert_eq!(cpu.register_a, 0b0110_1010);
    }

    #[test]
    fn test_inc_zero_page() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x01);
        cpu.load_and_run(vec![0xe6, 0x10, 0x00]);

        assert_eq!(cpu.mem_read(0x10), 0x02);
    }

    #[test]
    fn test_lsr_on_reg_a() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0001, 0x4a, 0x00]);

        assert_eq!(cpu.register_a, 0b0000_0000);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_ora_with_zero_result() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0000, 0x09, 0b0000_0000, 0x00]);

        assert_eq!(cpu.register_a, 0b0000_0000);
        assert!(cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ora_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_0000, 0x09, 0b0000_0001, 0x00]);

        assert_eq!(cpu.register_a, 0b1111_0001);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_pha() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_0000, 0x48, 0x00]);

        assert_eq!(cpu.mem_read(STACK as u16 + cpu.stack_pointer as u16 + 1), 0b1111_0000);
    }

    #[test]
    fn test_php() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_0000, 0x48, 0x00]);

        assert_eq!(cpu.mem_read(STACK as u16 + cpu.stack_pointer as u16 + 1), 0b1111_0000);
    }

    #[test]
    fn test_pla() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_0000, 0x48, 0xa9, 0b0000_0000, 0x68, 0x00]);

        assert_eq!(cpu.register_a, 0b1111_0000);
    }

    #[test]
    fn test_plp() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_1111, 0x48, 0x28, 0x00]);

        assert_eq!(cpu.status.bits(), 0b1100_1111);
    }

    #[test]
    fn test_rol_on_reg_a() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1000_0000, 0x2a, 0x00]);

        assert_eq!(cpu.register_a, 0b0000_0000);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_ror_on_reg_a() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0001, 0x6a, 0x00]);

        assert_eq!(cpu.register_a, 0b0000_0000);
        assert!(cpu.status.contains(CpuFlags::CARRY));
    }

    #[test]
    fn test_rti() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_1111, 0x48, 0x40, 0x00]);

        assert_eq!(cpu.status.bits(), 0b0000_1111);
    }

    #[test]
    fn test_stx() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_1111, 0xaa, 0x86, 0x10, 0x00]);

        assert_eq!(cpu.mem_read(0x10), 0b0000_1111);
    }

    #[test]
    fn test_sty() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_1111, 0xa8, 0x84, 0x10, 0x00]);

        assert_eq!(cpu.mem_read(0x10), 0b0000_1111);
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1111_1111, 0x29, 0b0000_1111, 0x00]);

        assert_eq!(cpu.register_a, 0b0000_1111);
    }

    #[test]
    fn test_clc() {
        let mut cpu = CPU::new();
        cpu.status.insert(CpuFlags::CARRY);
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0xff, 0x18, 0x00]);

        assert!(!cpu.status.contains(CpuFlags::CARRY));
    }
}
