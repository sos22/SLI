/* Operand sizes: 8-bit operands or specified/overridden size. */
#define ByteOp      (1<<0) /* 8-bit operands. */
/* Source operand type. */
#define SrcImm      (5<<3) /* Immediate operand. */
#define SrcImmByte  (6<<3) /* 8-bit sign-extended immediate operand. */
#define SrcMask     (7<<3)
/* Generic ModRM decode. */
#define ModRM       (1<<6)

#define Valid       (1<<1)

static uint8_t opcode_table[256] = {
    /* 0x00 - 0x07 */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, Valid, Valid,
    /* 0x08 - 0x0F */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, Valid, 0,
    /* 0x10 - 0x17 */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, Valid, Valid,
    /* 0x18 - 0x1F */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, Valid, Valid,
    /* 0x20 - 0x27 */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, 0, Valid,
    /* 0x28 - 0x2F */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, 0, Valid,
    /* 0x30 - 0x37 */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, 0, Valid,
    /* 0x38 - 0x3F */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|SrcImm, SrcImm, 0, Valid,
    /* 0x40 - 0x4F */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x50 - 0x5F */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x60 - 0x67 */
    Valid, Valid, ModRM, ModRM,
    0, 0, 0, 0,
    /* 0x68 - 0x6F */
    Valid, SrcImm|ModRM,
    Valid, SrcImmByte|ModRM,
    Valid, Valid, Valid, Valid,
    /* 0x70 - 0x77 */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x78 - 0x7F */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x80 - 0x87 */
    ByteOp|SrcImm|ModRM, SrcImm|ModRM,
    ByteOp|SrcImm|ModRM, SrcImmByte|ModRM,
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    /* 0x88 - 0x8F */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    /* 0x90 - 0x97 */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x98 - 0x9F */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0xA0 - 0xA7 */
    ByteOp|Valid, Valid,
    ByteOp|Valid, Valid,
    ByteOp|Valid, Valid,
    ByteOp|Valid, Valid,
    /* 0xA8 - 0xAF */
    ByteOp|SrcImm, SrcImm,
    ByteOp|Valid, Valid,
    ByteOp|Valid, Valid,
    ByteOp|Valid, Valid,
    /* 0xB0 - 0xB7 */
    ByteOp|SrcImm|Valid, ByteOp|SrcImm|Valid,
    ByteOp|SrcImm|Valid, ByteOp|SrcImm|Valid,
    ByteOp|SrcImm|Valid, ByteOp|SrcImm|Valid,
    ByteOp|SrcImm|Valid, ByteOp|SrcImm|Valid,
    /* 0xB8 - 0xBF */
    SrcImm|Valid, SrcImm|Valid, SrcImm|Valid, SrcImm|Valid,
    SrcImm|Valid, SrcImm|Valid, SrcImm|Valid, SrcImm|Valid,
    /* 0xC0 - 0xC7 */
    ByteOp|SrcImm|ModRM, SrcImmByte|ModRM,
    Valid, Valid,
    ModRM, ModRM,
    ByteOp|SrcImm|ModRM, SrcImm|ModRM,
    /* 0xC8 - 0xCF */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0xD0 - 0xD7 */
    ByteOp|ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    Valid, Valid, Valid, Valid,
    /* 0xD8 - 0xDF */
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    /* 0xE0 - 0xE7 */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0xE8 - 0xEF */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0xF0 - 0xF7 */
    0, Valid, 0, 0,
    Valid, Valid,
    ByteOp|ModRM, ModRM,
    /* 0xF8 - 0xFF */
    Valid, Valid, Valid, Valid,
    Valid, Valid, ByteOp|ModRM, ModRM
};

static uint8_t twobyte_table[256] = {
    /* 0x00 - 0x07 */
    ModRM, ModRM, 0, 0, 0, Valid, Valid, 0,
    /* 0x08 - 0x0F */
    Valid, Valid, 0, 0, 0, ModRM, 0, 0,
    /* 0x10 - 0x17 */
    ModRM, ModRM, ModRM, ModRM, ModRM, ModRM, ModRM, ModRM,
    /* 0x18 - 0x1F */
    ModRM, ModRM, ModRM, ModRM,
    ModRM, ModRM, ModRM, ModRM,
    /* 0x20 - 0x27 */
    ModRM, ModRM, ModRM, ModRM,
    0, 0, 0, 0,
    /* 0x28 - 0x2F */
    ModRM, ModRM, ModRM, ModRM, ModRM, ModRM, ModRM, ModRM,
    /* 0x30 - 0x37 */
    Valid, Valid, Valid, 0,
    Valid, Valid, 0, 0,
    /* 0x38 - 0x3F */
    0, 0, 0, 0, 0, 0, 0, 0,
    /* 0x40 - 0x47 */
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    /* 0x48 - 0x4F */
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    /* 0x50 - 0x5F */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* 0x60 - 0x6F */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ModRM,
    /* 0x70 - 0x7F */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ModRM,
    /* 0x80 - 0x87 */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x88 - 0x8F */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0x90 - 0x97 */
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    /* 0x98 - 0x9F */
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    ByteOp|ModRM, ByteOp|ModRM,
    /* 0xA0 - 0xA7 */
    Valid, Valid, Valid, ModRM,
    ModRM, ModRM, 0, 0,
    /* 0xA8 - 0xAF */
    Valid, Valid, 0, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    /* 0xB0 - 0xB7 */
    ByteOp|ModRM, ModRM,
    ModRM, ModRM,
    ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    /* 0xB8 - 0xBF */
    0, 0, SrcImmByte|ModRM, ModRM,
    ModRM, ModRM,
    ByteOp|ModRM, ModRM,
    /* 0xC0 - 0xC7 */
    ByteOp|ModRM, ModRM,
    0, ModRM,
    0, 0, 0, ModRM,
    /* 0xC8 - 0xCF */
    Valid, Valid, Valid, Valid,
    Valid, Valid, Valid, Valid,
    /* 0xD0 - 0xDF */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* 0xE0 - 0xEF */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* 0xF0 - 0xFF */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
