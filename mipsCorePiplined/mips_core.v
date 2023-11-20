`timescale 1 ns/10 ps  // time-unit = 1 ns, precision = 10 ps
module mips_core (clk, rst, iaddr, idata, daddr, dwr, ddout, ddin);
	input  clk;
	input  rst;
	output reg [5:0]  iaddr;
	input  [31:0] idata;
	output [5:0]  daddr;
	output [31:0] ddout;
	input  [31:0] ddin;
	output        dwr;
	
	
	//Fetch signals
	reg [31:0] nextPC;
	reg [31:0] f_pc;
	reg [31:0] f_ir;
	
	wire [31:0] branch_value;
	wire [31:0] jump_value;
	//Fetch signals
	
	
	
	//Decode signals
	wire [5:0] 	d_op;
	wire [15:0] d_imm16;
	wire [31:0] d_imm32;
	wire [4:0]  d_rs;
	wire [4:0]  d_rt;
	wire [4:0]  d_rd;
	wire [31:0] d_regA;
	wire [31:0] d_regB;
	reg  [31:0] d_pc;
	reg  [31:0] d_ir;
	
	reg	 	   d_RegWrite;
	reg	 	   d_MemtoReg;
	reg	 	   d_MemWrite;
	reg	 	   d_MemRead;
	reg  [4:0] d_AluOp;
	reg  	   d_AluSrc;
	reg  	   d_RegDst;
	reg  	   d_Branch;
	reg			d_jump;
	reg			jalrOrJr;
	//Decode singnals
	
	// Execute singnals
	reg  [31:0] x_regA;
	reg  [31:0] x_regB;
	reg  [31:0] x_pc;

	wire signed [31:0] aluA;
	wire signed [31:0] aluB;
	reg  signed [31:0] aluZ;
	
	wire		[31:0] aluAu;
	wire		[31:0] aluBu;
	reg 		[31:0] aluZu;
	reg 		carry;	
	reg			equal;
	reg  [5:0]  alu_func;
	wire [5:0] 	x_funct;
	wire [4:0] 	shamt;
	wire 		PCSrc;
		
	reg  	   x_RegWrite;
	reg   	   x_MemtoReg;
	reg  	   x_MemWtite;
	reg	 	   x_MemRead;
	reg  [4:0] x_AluOp;
	reg  	   x_AluSrc;
	reg  	   x_RegDst;
	reg  	   x_Branch;
	reg	 [5:0] x_op;

	reg  [4:0]  x_rs;
	reg  [4:0]  x_rt;
	reg  [4:0]  x_rd;
	wire [4:0]  x_regtoWrite;
	reg  [31:0] x_imm32;
	
	reg [1:0] forwardA;
	reg [1:0] forwardB;

	reg		  stall_LW;
	// Execute signals
	
	//Memory signals
	reg  [31:0] m_addr;
	reg  [31:0] m_din;
	wire [31:0] m_dout;
	
	reg  [4:0]  m_regtoWrite;
	reg         m_RegWrite;
	reg	 	    m_MemRead;
	reg         m_MemtoReg;
	reg         m_MemWtite;
	
	//Memory signals
	
	
	//Write back signals
	reg  [31:0] w_mem_data;  // <- ddin
	reg  [31:0] w_AluZ;
	reg  [4:0]  w_regtoWrite;
	reg  		w_RegWrite;
	reg 		w_MemtoReg;
	wire [31:0] WB;
	
	//Write back signals
	
	
	
	reg [31:0] RegBank [0:33]; // 32 rows of 32-bits

	//***********************	
	// Registers
	//***********************	
	always @(posedge clk)
	begin
		forwardA <= 0;
		forwardB <= 0;
		
		stall_LW <= 0;
		jalrOrJr 	= 0;
		if(rst)
			begin	
				nextPC 	<= 0;
				f_pc 	<= 0;
				equal 	<= 0;
				iaddr 	<= 0;
				d_jump 	<= 0;
			end
		else
		begin
			if(stall_LW)
			begin
				//pc -> fetch //STALL
			
				//fetch -> decode //STALL
				
				//decode -> execute //STALL
				x_RegDst 	<= 0;
				x_Branch 	<= 0;
				x_MemRead 	<= 0;
				x_MemtoReg	<= 0;
				x_AluOp 	<= 5'b11000;//nop
				x_MemWtite 	<= 0;
				x_AluSrc 	<= 0;
				x_RegWrite 	<= 0;
				x_pc 		<= 32'd0;
				x_regA 		<= 32'd0;
				x_regB 		<= 32'd0;
				x_imm32 	<= 32'd0;
				x_rs 		<= 5'd0;
				x_rt 		<= 5'd0;
				x_rd 		<= 5'd0;
				x_op 		<= 6'd0;
			end
			else
			begin
				//pc -> fetch
				f_pc <= nextPC;

				//fetch -> decode
				if(PCSrc || d_jump)//STALL on branch
				begin
					d_pc <= 0;
					d_ir <= 0;
				end
				else
				begin
					d_pc <= f_pc;
					d_ir <= f_ir;
				end
				
				//decode -> execute
				x_RegDst <= d_RegDst;
				x_Branch <= d_Branch;
				x_MemRead <= d_MemRead;
				x_MemtoReg <= d_MemtoReg;
				x_AluOp <= d_AluOp;
				x_MemWtite <= d_MemWrite;
				x_AluSrc <= d_AluSrc;
				x_RegWrite <= d_RegWrite;
				x_pc <= d_pc;
				x_regA <= d_regA;
				x_regB <= d_regB;
				x_imm32 <= d_imm32;
				x_rs <= d_rs;
				x_rt <= d_rt;
				x_rd <= d_rd;
				x_op <= d_op;
			end
			
			//execute -> memory
			m_RegWrite <= x_RegWrite;
			m_MemtoReg <= x_MemtoReg;
			m_MemRead <= x_MemRead;
			m_MemWtite <= x_MemWtite;
			if((x_op == 6'b000000 && (x_funct == 6'b100001 || x_funct == 6'b100011)) || x_op == 6'b001001)
				m_addr <= aluZu;
			else
				m_addr <= aluZ;
			m_din <= x_regB;
			m_regtoWrite <= x_regtoWrite;
			
			
			//memory -> write back
			w_MemtoReg <= m_MemtoReg;
			w_RegWrite <= m_RegWrite;
			w_mem_data <= m_dout;
			w_AluZ <= m_addr;
			w_regtoWrite <= m_regtoWrite;
			
		end
	end
		


	// Fetch *********************** Fetch
	always @(*)begin 
		begin 
			//temp_npc <= PCSrc ? pc_branch + 1 : f_pc + 1;	
			if(d_jump)
			begin
				iaddr <= jump_value[5:0];
				f_pc  <= iaddr;
				nextPC <= jump_value + 1;
			end 
			else
			begin
				iaddr <= f_pc[5:0];
				nextPC <= PCSrc ? branch_value + 1 : f_pc + 1;

			end
			f_ir <= idata;
		end
	end
	// assign temp_npc = d_jump ? jump_value : temp_npc2;
	// assign nextPC = PCSrc ? branch_value + 1 : f_pc + 1;
	// assign iaddr = f_pc[5:0];
	// assign f_ir = idata;
	// Fetch *********************** Fetch
	
	

	// Decode ********************** Decode 
	assign d_op	 	= d_ir[31:26];
	assign d_rs    	= d_ir[25:21];
	assign d_rt    	= d_ir[20:16];
	assign d_rd		= d_ir[15:11];
	assign d_imm16 	= d_ir[15:0];
	assign d_imm32 	= d_imm16[15] ? {16'hffff,d_imm16[15:0]} : {16'h0000,d_imm16[15:0]};
	assign branch_value[31:0] = d_imm32[31:0] + d_pc[31:0];
	assign jump_value = jalrOrJr ? x_regA : {d_pc[31:26],d_ir[25:0]};
	
	always @(*)//Control Path
	begin
		
		case (d_op)
			6'b000000: begin	// R-Type
				d_RegDst 	<= 1;
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_AluSrc 	<= 0;
				d_RegWrite 	<= 1;
				d_jump 		<= 0;
				d_AluOp 	<= 5'b00010;
			end
			6'b000100:	// BEQ
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 1;
				d_jump 		<= 0;
				d_AluOp		<= 5'b00001;
			end
			6'b000001: //bgez,bgezal,bltzal
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 1;
				d_jump 		<= 0;
				d_AluOp		<= 5'b10101;
			end
			6'b000110: //blez
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 1;
				d_jump 		<= 0;
				d_AluOp		<= 5'b10111;
			end
			6'b000111: //bgtz
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 1;
				d_jump 		<= 0;
				d_AluOp		<= 5'b10110;
			end
			6'b000101://bne
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 1;
				d_jump 		<= 0;
				d_AluOp		<= 5'b00111;
			end
			6'b101011: //SW
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 1;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 1;
				d_Branch	<= 0;
				d_jump 		<= 0;
				d_AluOp		<= 5'b00000;
			end
			6'b100011: //LW
			begin
				d_RegDst 	<= 0;
				d_AluSrc  	<= 1;
				d_MemtoReg	<= 1;
				d_RegWrite	<= 1;
				d_MemRead	<= 1;
				d_MemWrite	<= 0;
				d_Branch	<= 0;
				d_jump 		<= 0;
				d_AluOp		<= 5'b00000;
			end
			6'b000010: //j
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 0;
                d_jump 		<= 1;
            end
			6'b000011://jal
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 0;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 0;
                d_jump 		<= 1;
				RegBank[31] = d_pc;
			end
			6'b001000://addi
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 1;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 1;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 0;
                d_jump 		<= 0;
				d_AluOp		<= 5'b00000;	
			end
			6'b001001://addiu
			begin
				d_RegDst 	<= 0;
				d_AluSrc 	<= 1;
				d_MemtoReg	<= 0;
				d_RegWrite	<= 1;
				d_MemRead	<= 0;
				d_MemWrite	<= 0;
				d_Branch	<= 0;
                d_jump 		<= 0;
				d_AluOp		<= 5'b10010;
			end
			6'b011100://mul
			begin
				d_RegDst 	<= 1;
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_AluSrc 	<= 0;
				d_RegWrite 	<= 1;
				d_jump 		<= 0;
				d_AluOp 	<= 5'b00011;
			end
			6'b001100://andi
			begin
				d_RegDst 	<= 0;
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_AluSrc 	<= 1;
				d_RegWrite 	<= 1;
				d_jump 		<= 0;
				d_AluOp 	<= 5'b00100;
			end	
			6'b001101://ori
			begin
				d_RegDst 	<= 0;
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_AluSrc 	<= 1;
				d_RegWrite 	<= 1;
				d_jump 		<= 0;
				d_AluOp 	<= 5'b00101;
			end
			6'b001111://lui
			begin
				d_RegDst 	<= 0;
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_AluSrc 	<= 1;
				d_RegWrite 	<= 1;
				d_jump 		<= 0;
				d_AluOp 	<= 5'b00110;
			end
			6'b001010://slti 
			begin
				d_AluSrc 	<= 1;
				d_MemtoReg 	<= 0;
				d_RegDst 	<= 0;
				d_MemWrite 	<= 0;
				d_MemRead 	<= 0;
				d_Branch 	<= 0;
				d_RegWrite	<= 1;
				d_AluOp 	<= 5'b01000;
			end
			6'b001010://sltiu 
			begin
				d_AluSrc 	<= 1;
				d_MemtoReg 	<= 0;
				d_RegDst 	<= 0;
				d_MemWrite 	<= 0;
				d_MemRead 	<= 0;
				d_Branch 	<= 0;
				d_RegWrite	<= 1;
				d_AluOp 	<= 5'b10100;
			end
			6'b001110://xori
			begin
				d_AluSrc 	<= 1;
				d_MemtoReg 	<= 0;
				d_RegDst 	<= 0;
				d_MemWrite 	<= 0;
				d_MemRead 	<= 0;
				d_Branch 	<= 0;
				d_RegWrite	<= 1;
				d_AluOp 	<= 5'b10011;
			end
			default:
			begin
				alu_func 	= 6'b011000;//nop
				d_Branch 	<= 0; 
				d_MemRead 	<= 0;
				d_MemtoReg 	<= 0;
				d_MemWrite 	<= 0;
				d_RegWrite 	<= 0;
				d_RegDst 	<= 0;
				d_AluSrc 	<= 0;
				d_jump 		<= 0;
				jalrOrJr 	<= 0;
			end
		endcase	
		
		case (d_AluOp)
			5'b00001://beq
				equal = (d_regA == d_regB);
			5'b10101:
			begin
				case(d_rt)
					5'b00001://bgez
						equal = (d_regA >= 0);

					5'b10001://bgezal
					begin
						equal = (d_regA >= 0);
						RegBank[31] = d_pc;
					end
					5'b10000://bltzal
					begin
						equal = (d_regA < 0);
						RegBank[31] = d_pc;
					end
					5'b00000://bltz
						equal = (d_regA < 0);
				endcase
			end
			5'b10111://blez
				equal = (d_regA <= 0);
			5'b10110://bgtz
				equal = (d_regA > 0);
			5'b00111://bne
				equal = (d_regA - d_regB != 0);
		endcase
	end

	// Register bank
	assign d_regA = RegBank[d_rs];
	assign d_regB = RegBank[d_rt];
	always @(posedge clk)
	begin
		if (w_RegWrite)
			RegBank[w_regtoWrite] = WB;
		RegBank[0] = 32'd0;
		//RegBank[1] = 32'h0000000A;
		//RegBank[2] = 32'h00000002;
	end
	// Decode ********************** Decode
	
	


	// Execute ********************* Execute
	assign PCSrc = d_Branch & equal;
	assign aluA = (forwardA == 2'b01) ? WB :((forwardA == 2'b10) ? m_addr :  x_regA);
	assign aluAu = (forwardA == 2'b01) ? WB :((forwardA == 2'b10) ? m_addr :  x_regA);
	assign aluB = (x_AluSrc? x_imm32 : ((forwardB == 2'b01) ? WB :((forwardB == 2'b10) ? m_addr : x_regB)));
	assign aluBu = (x_AluSrc? x_imm32 : ((forwardB == 2'b01) ? WB :((forwardB == 2'b10) ? m_addr : x_regB)));
	assign x_regtoWrite = x_RegDst ? x_rd : x_rt;
	assign x_funct = x_imm32[5:0];
	assign shamt = x_imm32[10:6];
	
	always @(*)//ALU control
	begin
		case(x_AluOp)
			5'b00000:// SW & LW & addi
			begin
				alu_func = 6'b000000;
			end
			5'b00010: //R-Type
				case (x_funct)
					6'b100000: 	// add
						alu_func = 6'b000000;
					6'b100001: 	// addu
						alu_func = 6'b000001;
					6'b100100: 	// and
						alu_func = 6'b000010;
					6'b100101: 	// or
						alu_func = 6'b000110;
					6'b100010: 	// sub
						alu_func = 6'b001001;
					6'b100011: 	// subu
						alu_func = 6'b001010;
					6'b000010: //srl
						alu_func = 6'b001000;
					6'b000110: //srlvx
						alu_func = 6'b010001;
					6'b000000: //sll
						alu_func = 6'b000111;
					6'b000100: //sllv
						alu_func = 6'b010000;
					6'b000011: //sra
						alu_func = 6'b000011;
					6'b000111: //srav
						alu_func = 6'b000100;
					6'b011011://divu
						alu_func = 6'b001101;
					6'b101010://slt
						alu_func = 6'b001111;
					6'b101011://sltu
						alu_func = 6'b010011;
					6'b100111://nor
						alu_func = 6'b000101;
					6'b100110: //xor
						alu_func = 6'b001011;
					6'b001001: //jalr
					begin
						jalrOrJr = 1;
						RegBank[31] = nextPC;	
					end
					6'b001000://jr
						jalrOrJr = 1;
				endcase
			
			5'b00011://mul
				case(x_funct)
					6'b000010: alu_func = 6'b001100;
				endcase
			
			5'b00100: //andi
				alu_func = 6'b000010;
				
			5'b00101: //ori
				alu_func = 6'b000110;
			
			5'b00110://lui
				alu_func = 6'b001110;
			
			5'b01000: //slti
				alu_func = 6'b001111;
			5'b10100: //sltiu
				alu_func = 	6'b010011;
			
			5'b10010://addiu
				alu_func = 6'b000001;
			5'b10011://xori
				alu_func = 6'b001011;

			5'b11000: //nop
				alu_func = 6'b011000;
		endcase
	end
	
	always @(*)//ALU
	begin
		case (alu_func)
			6'b000000:	{carry,aluZ} = aluA + aluB; //add			
			6'b000001:	aluZu = aluAu + aluBu;		//addu		
			6'b000010:	aluZ = aluA & aluB;			//and
			6'b000011:	aluZ = aluB >>> shamt; 		//sra
			6'b000100:	aluZ = aluB >>> aluA[4:0]; 	//srav
			6'b000101:	aluZ = ~(aluA | aluB);		//nor
			6'b000110:	aluZ = aluA | aluB;			//or
			6'b000111:	aluZ = aluB << shamt;		//sll
			6'b010000:	aluZ = aluB << aluA[4:0];	//sllv
			6'b001000:	aluZ = aluB >> shamt;		//srl
			6'b010001:	aluZ = aluB >> aluA[4:0]; 	//srlv
			6'b001001:	{carry,aluZ} = aluA - aluB;	//sub
			6'b001010:	aluZu = aluAu - aluBu;		//subu
			6'b001011:	aluZ = aluA ^ aluB;			//xor
			6'b001100:	aluZ = aluA * aluB;	 		//mul
			6'b001101:	begin						//divu
						RegBank[32] = aluA / aluB;		
						RegBank[33] = aluA % aluB;
						end
			6'b001110:	aluZ = {aluB[15:0],16'h0000};//lui
			6'b001111:	aluZ = aluB > aluA ? 1 : 0;  //slt
			6'b010011:	aluZu = aluBu > aluAu ? 1 : 0;//sltu
			6'b011000: 	aluZ = 32'd0;				//nop
			
			default:	aluZ = 32'd0;				
		endcase
	end

	always @(m_RegWrite, w_RegWrite, m_regtoWrite, w_regtoWrite, x_rs, x_rt)//forward unit
	begin
		//MEM hazard
		if(m_RegWrite 
			&& m_regtoWrite != 5'b00000 
			&& m_regtoWrite == x_rs)
			forwardA = 2'b10;

		if(m_RegWrite
			&& m_regtoWrite != 5'b00000 
			&& m_regtoWrite == x_rt)
			forwardB = 2'b10;

		//WB hazard
		if(w_RegWrite 
			&& w_regtoWrite != 5'b00000 
			&& m_regtoWrite != x_rs 
			&& w_regtoWrite == x_rs)
			forwardA = 2'b01; 

		if(w_RegWrite
			&& w_regtoWrite != 5'b00000
			&& m_regtoWrite != x_rt
			&& w_regtoWrite == x_rt)
			forwardB = 2'b01;
	end

	always @(x_MemRead, x_rt, d_rs, d_rt)//HAZARD detection unit
	begin
		if(x_MemRead
			&& (x_rt == d_rs
				|| x_rt == d_rt))
			stall_LW = 1;	
	end
	// Execute ********************* Execute
	
	//memory
	assign daddr = m_addr[5:0];
	assign ddout  = m_din;
	assign m_dout = ddin;
	assign dwr = m_MemWtite;
	
	
	//write back
	assign WB = w_MemtoReg ? w_mem_data : w_AluZ;

endmodule 

