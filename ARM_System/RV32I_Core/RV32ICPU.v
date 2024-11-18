`timescale 1ns/1ns

/* WARNING: DO NOT MODIFY THE PREDEFINED NAMES OF THE MODULES AND THE PORTS! */
/* NOTE: YOU CAN ADD NEW MODULES, PORTS, WIRES, AND REGISTERS AS NEEDED! */

//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R		      7'b0110011
`define OP_I_Arith    7'b0010011
`define OP_I_Load     7'b0000011
`define OP_I_JALR     7'b1100111
`define OP_S          7'b0100011
`define OP_B          7'b1100011
`define OP_U_LUI      7'b0110111
`define OP_U_AUIPC    7'b0010111
`define OP_J_JAL      7'b1101111

module maindec(input        rst,
               input        clk,
               input  [6:0] opcode,
               output [1:0] ALUSrcA,
               output [1:0] ALUSrcB,
               output       IRWrite,
               output       PCWrite,
               output [1:0] ResultSrc,
               output       RegWrite,
               output       MemWrite,
               output       branch,
               output reg   ALUOp);  // ALU는 Fetch 단계에서 덧셈을 수행해야 함, ALUOp = 1이면 덧셈

  reg [3:0] state, n_state;

  // 상태 정의
  localparam IF        = 4'b0000;  // 명령어 페치
  localparam Decode    = 4'b0001;  // 명령어 디코드
  localparam ExR       = 4'b0010;  // R-타입 실행
  localparam ExI       = 4'b0011;  // I-타입 산술 실행
  localparam ExL       = 4'b0100;  // 로드 실행
  localparam ExS       = 4'b0101;  // 스토어 실행
  localparam ExB       = 4'b0110;  // 분기 실행
  localparam MemAccessL= 4'b0111;  // 로드 메모리 액세스
  localparam MemAccessS= 4'b1000;  // 스토어 메모리 액세스
  localparam WB_R      = 4'b1001;  // R-타입 쓰기 백
  localparam WB_I      = 4'b1010;  // I-타입 쓰기 백
  localparam WB_L      = 4'b1011;  // 로드 쓰기 백
  localparam ExJ       = 4'b1100;  // 점프 실행 (JAL)
  localparam ExJr      = 4'b1101;  // 점프 실행 (JALR)

  reg [10:0] controls;

  assign {ALUSrcA, ALUSrcB, IRWrite, PCWrite, ResultSrc, RegWrite, MemWrite, branch} = controls;

  always @(negedge clk, negedge rst) begin
    if(!rst)
      state <= IF;
    else
      state <= n_state;
  end

  // 상태에 따른 제어 신호 설정
  always @(*) begin
    case(state)
    IF:	begin
      controls <= 11'b00_10_11_00_000; // ALUSrcA=00(PC), ALUSrcB=10(4), IRWrite=1, PCWrite=1
      ALUOp <= 1;                      // 덧셈 수행, PC + 4
    end
    Decode:	begin
      controls <= 11'b01_01_00_00_000; // ALUSrcA=01(OldPC), ALUSrcB=01(imm)
      ALUOp <= 1;                      // 덧셈 수행, OldPC + imm
    end
    ExR:	begin
      controls <= 11'b10_00_00_00_000; // ALUSrcA=10(rs1), ALUSrcB=00(rs2)
      ALUOp <= 0;                      // ALUOp = 0이면 함수 단위에서 결정
    end
    ExI: begin
      controls <= 11'b10_01_00_00_000; // ALUSrcA=10(rs1), ALUSrcB=01(imm)
      ALUOp <= 0;
    end
    ExL: begin
      controls <= 11'b10_01_00_00_000; // ALUSrcA=10(rs1), ALUSrcB=01(imm)
      ALUOp <= 1;                      // 주소 계산을 위해 덧셈 수행
    end
    MemAccessL: begin
      controls <= 11'b00_00_00_00_000; // 제어 신호 없음
      ALUOp <= 0;
    end
    WB_L: begin
      controls <= 11'b00_00_00_00_110; // ResultSrc=01(MemData), RegWrite=1
      ALUOp <= 0;
    end
    ExS: begin
      controls <= 11'b10_01_00_00_000; // ALUSrcA=10(rs1), ALUSrcB=01(imm)
      ALUOp <= 1;                      // 주소 계산을 위해 덧셈 수행
    end
    MemAccessS: begin
      controls <= 11'b00_00_00_00_001; // MemWrite=1
      ALUOp <= 0;
    end
    ExB: begin
      controls <= 11'b10_00_00_00_000; // ALUSrcA=10(rs1), ALUSrcB=00(rs2)
      ALUOp <= 0;
      // 분기 판단은 데이터 경로에서 수행
    end
    ExJ: begin
      controls <= 11'b00_01_00_10_100; // ALUSrcA=00(PC), ALUSrcB=01(imm), PCWrite=1, ResultSrc=10, RegWrite=1
      ALUOp <= 1;                      // PC + imm 계산
    end
    ExJr: begin
      controls <= 11'b10_01_00_10_100; // ALUSrcA=10(rs1), ALUSrcB=01(imm), PCWrite=1, ResultSrc=10, RegWrite=1
      ALUOp <= 1;
    end
    WB_R: begin
      controls <= 11'b00_00_00_00_100; // RegWrite=1, ResultSrc=00(ALU 결과)
      ALUOp <= 0;
    end
    WB_I: begin
      controls <= 11'b00_00_00_00_100; // RegWrite=1, ResultSrc=00(ALU 결과)
      ALUOp <= 0;
    end
    default: begin
      controls <= 11'b00_00_00_00_000;
      ALUOp <= 0;
    end
    endcase
  end

  // 다음 상태 결정
  always @(*) begin
    case(state)
    IF:
    begin
      n_state <= Decode;
    end
    Decode:
    begin
      case(opcode)
        `OP_R:          n_state <= ExR;
        `OP_I_Arith:    n_state <= ExI;
        `OP_I_Load:     n_state <= ExL;
        `OP_S:          n_state <= ExS;
        `OP_B:          n_state <= ExB;
        `OP_J_JAL:      n_state <= ExJ;
        `OP_I_JALR:     n_state <= ExJr;
        `OP_U_LUI,
        `OP_U_AUIPC:    n_state <= WB_I;
        default:        n_state <= IF;
      endcase
    end
    ExR:
    begin
      n_state <= WB_R;
    end
    WB_R:
    begin
      n_state <= IF;
    end
    ExI:
    begin
      n_state <= WB_I;
    end
    WB_I:
    begin
      n_state <= IF;
    end
    ExL:
    begin
      n_state <= MemAccessL;
    end
    MemAccessL:
    begin
      n_state <= WB_L;
    end
    WB_L:
    begin
      n_state <= IF;
    end
    ExS:
    begin
      n_state <= MemAccessS;
    end
    MemAccessS:
    begin
      n_state <= IF;
    end
    ExB:
    begin
      n_state <= IF;
    end
    ExJ:
    begin
      n_state <= IF;
    end
    ExJr:
    begin
      n_state <= IF;
    end
    default:    n_state <= IF;
    endcase
  end

endmodule

//
// ALU 디코더는 ALU 제어 신호(alucontrol)를 생성합니다.
//
module aludec(input      [6:0] opcode,           // opcode
              input      [6:0] funct7,           // funct7
              input      [2:0] funct3,           // funct3
              input            ALUOp,
              output reg [4:0] alucontrol);      // ALU 제어 신호

  always @(*)
    if (ALUOp) alucontrol <= 5'b00000; // 덧셈
    else
    begin
      case(opcode)
        `OP_R:   		    // R-타입
        begin
          case({funct7,funct3})
          10'b0000000_000: alucontrol <= 5'b00000; // addition (add)
          10'b0100000_000: alucontrol <= 5'b10000; // subtraction (sub)
          10'b0000000_111: alucontrol <= 5'b00001; // and (and)
          10'b0000000_110: alucontrol <= 5'b00010; // or (or)
          default:         alucontrol <= 5'bxxxxx;
          endcase
        end

        `OP_I_Arith:    // I-타입 산술
        begin
          case(funct3)
          3'b000:  alucontrol <= 5'b00000; // addi
          3'b110:  alucontrol <= 5'b00010; // ori
          3'b111:  alucontrol <= 5'b00001; // andi
          default: alucontrol <= 5'bxxxxx;
          endcase
        end

        `OP_I_Load: 	  // I-타입 로드 (LW, LH, LB...)
        alucontrol <= 5'b00000; //add

        `OP_I_JALR:		  // I-타입 JALR
        alucontrol <= 5'b00000; //add

        `OP_B:   		    // B-타입 분기 (BEQ, BNE, ...)
        alucontrol <= 5'b10000; //sub

        `OP_S:   		    // S-타입 스토어 (SW, SH, SB)
        alucontrol <= 5'b00000; //add

        `OP_U_LUI: 		  // U-타입 (LUI)
        alucontrol <= 5'b00000; //add

        `OP_U_AUIPC:
        alucontrol <= 5'b00000; //add

        default:
          alucontrol <= 5'b00000;
      endcase
    end

endmodule


//
// CPU 데이터 경로
//
module datapath(input         clk, reset_n, // 클럭 및 리셋 신호
                input  [31:0] inst,         // 입력 명령어
                input         regwrite,     // 레지스터 쓰기
                input  [4:0]  alucontrol,   // ALU 제어 신호
                input         branch,       // 분기
                input         PCWrite, IRWrite,    // PC, 명령어 레지스터 쓰기
                input  [1:0]  ALUSrcA, ALUSrcB, ResultSrc,  // 멀티플렉서 제어
                output reg [31:0] pc,       // 프로그램 카운터
                output reg [31:0] rd_data,
                output [31:0] aluout,       // ALU 출력
                output [31:0] MemWdata,     // 메모리에 쓸 데이터
                input  [31:0] MemRdata,     // 메모리에서 읽은 데이터
                input  [31:0] OldPC);       // 현재 PC 저장

  wire [4:0]  rs1, rs2, rd;               // 레지스터 주소
  wire [6:0]  opcode;                     // opcode
  wire [2:0]  funct3;                     // funct3
  wire [31:0] rs1_data, rs2_data;         // 레지스터 파일에서 읽은 데이터
  wire [20:1] jal_imm;                    // JAL 즉시값
  wire [31:0] se_jal_imm;                 // 부호 확장된 JAL 즉시값
  wire [12:1] jalr_imm;                   // JALR 즉시값
  wire [31:0] se_jalr_imm;                // 부호 확장된 JALR 즉시값
  wire [12:1] br_imm;                     // 분기 즉시값
  wire [31:0] se_br_imm;                  // 부호 확장된 분기 즉시값
  wire [31:0] se_imm_itype;               // 부호 확장된 I-타입 즉시값
  wire [31:0] se_imm_stype;               // 부호 확장된 S-타입 즉시값
  wire [31:0] auipc_lui_imm;              // AUIPC 및 LUI 즉시값
  reg  [31:0] alusrc1;                    // ALU의 첫 번째 입력
  reg  [31:0] alusrc2;                    // ALU의 두 번째 입력
  reg  [31:0] rs1_data_reg, rs2_data_reg; // 레지스터 파일에서 읽은 데이터 저장
  reg  [31:0] aluout_reg;                 // ALU 출력 저장
  wire		  Nflag, Zflag, Cflag, Vflag;           // 플래그
  wire		  f3beq, f3bne, f3blt, f3bgeu;          // 분기를 위한 funct3
  wire		  beq_taken;                            // BEQ 분기 여부
  wire		  bne_taken;                            // BNE 분기 여부
  wire 		  bgeu_taken;                           // BGEU 분기 여부
  wire		  blt_taken;                            // BLT 분기 여부

  assign beq_taken  =  branch & f3beq & Zflag;
  assign bne_taken  =  branch & f3bne & ~Zflag;
  assign blt_taken  =  branch & f3blt & (Nflag != Vflag);
  assign bgeu_taken =  branch & f3bgeu & Cflag;

  assign MemWdata = rs2_data_reg;
  assign Memaddr = aluout_reg; // 메모리 주소는 ALU 출력

  // JAL 즉시값
  assign jal_imm[20:1] = {inst[31],inst[19:12],inst[20],inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // JALR 즉시값
  assign jalr_imm[12:1] = {inst[31:20]};
  assign se_jalr_imm[31:0] = {{19{jalr_imm[12]}},jalr_imm[12:1],1'b0};

  // 분기 즉시값
  assign br_imm[12:1] = {inst[31],inst[7],inst[30:25],inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};

	assign se_imm_itype[31:0] = {{20{inst[31]}},inst[31:20]};
	assign se_imm_stype[31:0] = {{20{inst[31]}},inst[31:25],inst[11:7]};
	assign auipc_lui_imm[31:0] = {inst[31:12],12'b0};

  /* ------------------------------------------------------------------------ */

  assign rs1 = inst[19:15];   // rs1 레지스터 주소
  assign rs2 = inst[24:20];
  assign rd  = inst[11:7];
  assign funct3  = inst[14:12];
  assign opcode  = inst[6:0];

  assign f3beq  = (funct3 == 3'b000); // BEQ
  assign f3bne  = (funct3 == 3'b001);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu = (funct3 == 3'b111);

  // 프로그램 카운터(PC) 로직
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n)
      pc <= 0;
    else if (PCWrite | beq_taken | bne_taken | blt_taken | bgeu_taken)
    begin
	    // 분기 또는 점프가 발생하면 ALU 출력으로 PC 업데이트
      pc <= aluout;
    end
  end

	// ALU의 첫 번째 입력 (alusrc1)
  always @(*)
  begin
    if      (ALUSrcA == 2'b00) alusrc1[31:0] = pc;
    else if (ALUSrcA == 2'b01) alusrc1[31:0] = OldPC;
    else if (ALUSrcA == 2'b10) alusrc1[31:0] = rs1_data_reg;
    else                       alusrc1[31:0] = 32'b0;
  end

  // ALU의 두 번째 입력 (alusrc2)
  always @(*)
  begin
    if      (ALUSrcB == 2'b00) alusrc2[31:0] = rs2_data_reg;
    else if (ALUSrcB == 2'b01) begin
      // opcode에 따라 즉시값 선택
      case(opcode)
        `OP_I_Arith,
        `OP_I_Load,
        `OP_I_JALR:    alusrc2[31:0] = se_imm_itype;
        `OP_S:         alusrc2[31:0] = se_imm_stype;
        `OP_B:         alusrc2[31:0] = se_br_imm;
        `OP_J_JAL:     alusrc2[31:0] = se_jal_imm;
        `OP_U_AUIPC,
        `OP_U_LUI:     alusrc2[31:0] = auipc_lui_imm;
        default:       alusrc2[31:0] = 32'b0;
      endcase
    end
    else if (ALUSrcB == 2'b10) alusrc2[31:0] = 32'd4;
    else                       alusrc2[31:0] = 32'b0;
  end

	// 레지스터 파일, 메모리, PC의 결과값 선택 (rd_data)
	always @(*)
	begin
		if	    (ResultSrc == 2'b00)  rd_data[31:0] = aluout;
		else if (ResultSrc == 2'b01)	rd_data[31:0] = MemRdata;
		else if (ResultSrc == 2'b10)	rd_data[31:0] = OldPC + 32'd4;
		else						                rd_data[31:0] = 32'b0;
	end

  // rs1_data_reg 업데이트
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n) rs1_data_reg <= 0;
    else          rs1_data_reg <= rs1_data;
  end

  // rs2_data_reg 업데이트
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n) rs2_data_reg <= 0;
    else          rs2_data_reg <= rs2_data;
  end

  // ALUOut 레지스터 업데이트
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n) aluout_reg <= 0;
    else          aluout_reg <= aluout;
  end

  regfile i_regfile(
    .clk			(clk),
    .we			  (regwrite),
    .rs1			(rs1),
    .rs2			(rs2),
    .rd			  (rd),
    .rd_data	(rd_data),
    .rs1_data	(rs1_data),
    .rs2_data	(rs2_data));

	alu i_alu(
		.a			  (alusrc1),
		.b			  (alusrc2),
		.alucont	(alucontrol),
		.result	  (aluout),
		.N			  (Nflag),
		.Z			  (Zflag),
		.C			  (Cflag),
		.V			  (Vflag));

endmodule

module RV32I (
		      input         clk, reset_n, // 클럭 및 리셋 신호
          output [31:0] pc,		  		// 명령어 페치를 위한 프로그램 카운터
          input  [31:0] inst, 			// 입력 명령어
          output [3:0] 	be,         // 바이트 인에이블 (사용하지 않음)
          output        Memwrite, 	// 메모리 쓰기 제어 신호
          output 				Memread,    // 메모리 읽기 제어 신호
          output [31:0] Memaddr,  	// 메모리 주소
          output [31:0] MemWdata, 	// 메모리에 쓸 데이터
          input  [31:0] MemRdata); 	// 메모리에서 읽은 데이터

  wire [4:0]  alucontrol;
  wire        IRWrite, PCWrite, RegWrite, MemWrite;
  wire [1:0]  ALUSrcA, ALUSrcB, ResultSrc;
  wire        branch;
  reg  [31:0] inst_reg, OldPC;
  reg  [31:0] MemRdata_reg;
  assign Memwrite = MemWrite;
  assign Memread = ~MemWrite;
  assign be = 4'b1111;

  // inst_reg 및 OldPC 레지스터 업데이트
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n)
    begin
      inst_reg <= 0;
      OldPC <= 0;
    end
    else if (IRWrite)
    begin
      inst_reg <= inst;
      OldPC <= pc;
    end
  end

  // MemRdata_reg 업데이트
  always @(negedge clk, negedge reset_n)
  begin
    if (!reset_n)  MemRdata_reg <= 0;
    else           MemRdata_reg <= MemRdata;
  end


  // 컨트롤러 인스턴스화
  controller i_controller(
    .opcode		  (inst_reg[6:0]),
		.funct7		  (inst_reg[31:25]),
		.funct3		  (inst_reg[14:12]),
    .reset_n    (reset_n),
    .clk        (clk),
    .inst       (inst_reg[31:0]),
		.alucontrol	(alucontrol),
    .ALUSrcA    (ALUSrcA),
    .ALUSrcB    (ALUSrcB),
    .IRWrite    (IRWrite),
    .PCWrite    (PCWrite),
    .ResultSrc  (ResultSrc),
    .RegWrite   (RegWrite),
    .MemWrite   (MemWrite),
    .branch     (branch));

  // 데이터 경로 인스턴스화
  datapath i_datapath(
		.clk				(clk),
		.reset_n		(reset_n),
		.branch			(branch),
		.regwrite		(RegWrite),
    .PCWrite    (PCWrite),
    .IRWrite    (IRWrite),
    .ALUSrcA    (ALUSrcA),
    .ALUSrcB    (ALUSrcB),
    .ResultSrc  (ResultSrc),
		.alucontrol	(alucontrol),
		.pc				  (pc),
    .rd_data    (Memaddr),
		.inst				(inst_reg),
		.aluout			(aluout),
		.MemWdata		(MemWdata),
		.MemRdata		(MemRdata_reg),
    .OldPC      (OldPC));

endmodule

//
// 명령어 디코더
// 데이터 경로를 위한 제어 신호 생성
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  input        reset_n,
                  input        clk,
                  input  [31:0] inst,
                  output [4:0] alucontrol,
                  output [1:0] ALUSrcA,
                  output [1:0] ALUSrcB,
                  output       IRWrite,
                  output       PCWrite,
                  output [1:0] ResultSrc,
                  output       RegWrite,
                  output       MemWrite,
                  output branch);

  maindec i_maindec(
    .rst       (reset_n),
    .clk       (clk),
    .opcode    (opcode),
    .ALUSrcA   (ALUSrcA),
    .ALUSrcB   (ALUSrcB),
    .IRWrite   (IRWrite),
    .PCWrite   (PCWrite),
    .ResultSrc (ResultSrc),
    .RegWrite  (RegWrite),
    .MemWrite  (MemWrite),
    .branch    (branch),
    .ALUOp     (ALUOp));

	aludec i_aludec(
		.opcode     (opcode),
		.funct7     (funct7),
		.funct3     (funct3),
    .ALUOp      (ALUOp),
		.alucontrol (alucontrol));

endmodule
