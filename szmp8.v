`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Description: szmp8 is clone of kcpsm6(version:KCPSM6_Release9_30Sept14)
//                      
// Engineer: szfpga(szfpga@gmail.com)
// Design Name: 
// Module Name:    szmp8 
// difference from picobalze(kcpsm6): 1.read_strobe is aheade of one clk compare with kcmps6,so szmp8 can 
//                                      read one port at one instruction cycle(2 clks)
//                                    2.the interrupt can not be interrupt those instrution
//                                      JUMP,JUMP Z(Z=1),JUMP NZ(Z=0),JUMP C(C=1),JUMP NC(C=0),JUMP@(sX,sY),                                    
//                                      CALL,CALL Z(Z=1),CALL NZ(Z=0),CALL C(C=1),CALL NC(C=0),CALL@(sX,sY),
//                                      RETURN,RETURN Z(Z=1),RETURN NZ(Z=0),RETURN C(C=1),RETURN NC(C=0),LOAD&RETURN sX,KK
//                                    3.when an Interrupt Service Routine (ISR) is runing, the IE flag(when ISR is runing,IE=0) can not be changed by ENABLE INTERRUPT
//                                      or DISABLE INTERRUPT, only can be changed with RETURNI ENABLE or RETURNI DISABLE
//////////////////////////////////////////////////////////////////////////////////
module szmp8#(
   parameter [7:0] 	hwbuild = 8'h00,
   parameter [11:0] interrupt_vector = 12'h3FF,
   parameter integer scratch_pad_memory_size = 64 
   )
(
   output [11:0]	address,
   input	 [17:0]    	instruction,
   output		bram_enable,
   input	 [7:0]	in_port,
   output [7:0]	out_port,
   output [7:0]	port_id,
   output		write_strobe,
   output		k_write_strobe,
   output		read_strobe, // difference from xilinx kcpsm6's read_strobe
   input			interrupt,
   output		interrupt_ack,
   input			sleep,
   input			reset,
   input			clk 
   );
/////////////////////////////////////////////// 
localparam n = scratch_pad_memory_size == 64 ? 6 :scratch_pad_memory_size == 128 ? 7 :scratch_pad_memory_size == 256 ? 8 : 0;
///////////////////////////////////////////
wire load,star,ands,ors,xors,add,sub;
wire test,compare,sl0,sl1,slx,sla,rl,sr0,sr1,srx,sra,rr,regbanka,regbankb;
wire inputsp,outputsp,outputk,store,fetch,dis_intr,ena_intr,reti_dis_intr,reti_ena_intr,jump,jumpz;
wire jumpnz,jumpc,jumpnc,jumpsxsy,call,callz,callnz,callc,callnc,callsxsy,ret,retz,retnz,retc,retnc,load_ret,hwbd;
wire[11:0] inst_embed_addr;
wire[3:0] sx,sy;
wire[11:0] kk;

wire sy_const,cy_flag;
wire c_flag,z_flag;
wire[7:0] sx_dout,sy_dout;
wire[7:0] sx_din;
wire[4:0] sx_waddr;
wire sx_wren;
wire bank;//0 banka,1 bankb
reg[5:0] stack_addra = 6'h3f;//point null address
reg stack_wrena = 1'b0;
wire[11:0] pop_pc;
reg ie_flag = 1'b0;
wire ena_ie,dis_ie;
reg stack_pointer_over;// up flow or down flow
reg[11:0] pc = 12'd0;
wire[11:0] next_pc;
reg[11:0] push_pc = 12'd0;
reg[2:0] interrupt_sync_reg = 3'h0;
reg internal_int_ack=1'b0;
reg internal_reset = 1'b1,internal_reset_tmp = 1'b1;
reg sync_sleep = 1'b0,sync_sleep_tmp = 1'b0; 
reg t_state = 1'b0,t_state_d1 = 1'b0,t_state_d2 = 1'b0;
wire push_stack,pop_stack,jump_cmd;
reg isp_runing = 1'b0;
wire internal_int;

reg[11:0] interrupt_pc_stack=12'd0;
reg reti_pop = 1'b0;
reg reti_bank=1'b0,reti_z_flag=1'b0,reti_c_flag=1'b0;
reg internal_int_ack_d1 = 1'b0;


///////////////////////////
szmp8_dec szmp8_dec_0(
   .instruction(instruction),
   .sy_const(sy_const),// 0 for sy, 1 for kk or pp or ss 
   .cy_flag(cy_flag),// for add addcy sub subcy compare comparecy test testcy,0 for add or sub or compare or test, 1 for addcy or subcy or comparecy or testcy
   .load(load),
   .star(star),
   .ands(ands),
   .ors(ors),
   .xors(xors),
   .add(add),
   .sub(sub),
   .test(test),
   .compare(compare),
   .sl0(sl0),
   .sl1(sl1),
   .slx(slx),
   .sla(sla),
   .rl(rl),
   .sr0(sr0),
   .sr1(sr1),
   .srx(srx),
   .sra(sra),
   .rr(rr),
   .regbanka(regbanka),
   .regbankb(regbankb),
   .inputsp(inputsp),
   .outputsp(outputsp),
   .outputk(outputk),
   .store(store),
   .fetch(fetch),
   .dis_intr(dis_intr),
   .ena_intr(ena_intr),
   .reti_dis_intr(reti_dis_intr),
   .reti_ena_intr(reti_ena_intr),
   .jump(jump),
   .jumpz(jumpz),
   .jumpnz(jumpnz),
   .jumpc(jumpc),
   .jumpnc(jumpnc),
   .jumpsxsy(jumpsxsy),
   .call(call),
   .callz(callz),
   .callnz(callnz),
   .callc(callc),
   .callnc(callnc),
   .callsxsy(callsxsy),
   .ret(ret),
   .retz(retz),
   .retnz(retnz),
   .retc(retc),
   .retnc(retnc),
   .load_ret(load_ret),
   .hwbd(hwbd),
   .inst_embed_addr(inst_embed_addr),
   .sx(sx),
   .sy(sy),
   .kk(kk)
   );

szmp8_alu#(
   .scratch_pad_memory_size(n),
   .hwbuild_parameter(hwbuild)
 )
szmp8_alu_0(
   .clk(clk),
   .rst(internal_reset|stack_pointer_over),
   .t_state_d1(t_state_d1),
   .t_state_d2(t_state_d2),
   .sy_const(sy_const),// 0 for sy, 1 for kk or pp or ss 
   .cy_flag(cy_flag),// for add addcy sub subcy compare comparecy test testcy,0 for add or sub or compare or test, 1 for addcy or subcy or comparecy or testcy
   .load(load),
   .star(star),
   .ands(ands),
   .ors(ors),
   .xors(xors),
   .add(add),
   .sub(sub),
   .test(test),
   .compare(compare),
   .sl0(sl0),
   .sl1(sl1),
   .slx(slx),
   .sla(sla),
   .rl(rl),
   .sr0(sr0),
   .sr1(sr1),
   .srx(srx),
   .sra(sra),
   .rr(rr),
   .load_ret(load_ret),
   .hwbd(hwbd),
	.regbanka(regbanka),
   .regbankb(regbankb),
   .inputsp(inputsp),
   .outputsp(outputsp),
   .outputk(outputk),
   .store(store),
   .fetch(fetch),
   .sx_ain(sx),
   .sx_din(sx_dout),
   .sy_din(sy_dout),
   .kk(kk),
   .in_port(in_port),
   .out_port(out_port),
   .port_id(port_id),
   .write_strobe(write_strobe),
   .k_write_strobe(k_write_strobe),
   .read_strobe(read_strobe),
	.reti_pop(reti_pop),//drive by t_state_d1
	.reti_bank(reti_bank),
	.reti_c_flag(reti_c_flag),
	.reti_z_flag(reti_z_flag),
   .sreg_bank(bank),
   .c_flag_out(c_flag),
   .z_flag_out(z_flag),
   .sx_aout(sx_waddr),//bit4 
   .sx_wren(sx_wren),
   .sx_dout(sx_din)
);
//////////////////////////////////////////////////////////
// for sx sy


ramnx8 #(
   .scratch_pad_memory_size(5), 
   .scratch_pad_memory_width(8)
   )
ramnx8_sx 
(
   .clka(clk),
   .addra(sx_waddr),
   .wrena(sx_wren),
   .dina(sx_din),
   .addrb({bank,sx}),
   .doutb(sx_dout)
   );
ramnx8 #(
   .scratch_pad_memory_size(5), //32,64,128,256
   .scratch_pad_memory_width(8)
   )
ramnx8_sy 
(
   .clka(clk),
   .addra(sx_waddr),
   .wrena(sx_wren),
   .dina(sx_din),
   .addrb({bank,sy}),
   .doutb(sy_dout)
   );
/////////////////////////////////////   
//////////////////////////////////////////////////////////



///////////////////////////////////////
// stack

ramnx8 #(
   .scratch_pad_memory_size(5),
   .scratch_pad_memory_width(12)
   )
ramnx8_stack 
(
   .clka(clk),
   .addra(stack_addra[4:0]),
   .wrena(stack_wrena),
   .dina(push_pc),
   .addrb(stack_addra[4:0]),
   .doutb(pop_pc)
   ); 
////////////////////////////////////////////////////////////////

assign address = pc;



/////////////////////////////////////////////////////////
// control
// pipe line for instruction run
// t_state: bram_enable;t_state_d1:instruction decode,t_state_d2:instruction run,
//  ie flag controll
// 


assign push_stack = call|callsxsy|(callz&z_flag)|(callnz&(~z_flag))|(callc&c_flag)|(callnc&(~c_flag)); 
assign pop_stack = load_ret|ret|(retz&z_flag)|(retnz&(~z_flag))|(retc&c_flag)|(retnc&(~c_flag));
assign jump_cmd = jump|(jumpz&z_flag)|(jumpnz&(~z_flag))|(jumpc&c_flag)|(jumpnc&(~c_flag))|jumpsxsy;
assign next_pc = pc+1'b1;
assign bram_enable = t_state;

assign dis_ie = (dis_intr&(~isp_runing)) | (reti_dis_intr&isp_runing) |(internal_int&ie_flag & (~isp_runing));
assign ena_ie = (ena_intr&(~isp_runing)) | (reti_ena_intr&isp_runing);
assign interrupt_ack = internal_int_ack;


always@(posedge clk)
begin
   sync_sleep_tmp <= sleep;
   sync_sleep <= sync_sleep_tmp;
   internal_reset_tmp <= reset;
   internal_reset <= internal_reset_tmp;
   interrupt_sync_reg <= {interrupt_sync_reg[1:0],interrupt};
end
assign internal_int = interrupt_sync_reg[1];

always@(posedge clk)
begin
   if(internal_reset == 1'b1 || (stack_pointer_over) == 1'b1)
      begin
         pc <= 12'd0;
         t_state <= 1'b0;
         t_state_d1 <= 1'b0;
         stack_addra <= 6'h3f;
         stack_wrena <= 1'b0;
         stack_pointer_over <= 1'b0;
         internal_int_ack <= 1'b0;
         ie_flag <= 1'b0;
         interrupt_pc_stack <= 12'd0;
         reti_pop <= 1'b0;
      end
   else
      begin
         t_state <= (~t_state) & (~sync_sleep);
         t_state_d1 <= t_state;
         t_state_d2 <= t_state_d1;
         if(t_state_d1 == 1'b1)
           begin
              case({push_stack,pop_stack,jump_cmd})
                  3'b100:begin
                            if(stack_addra == 6'h1f) // over flow
                               begin
                                  stack_pointer_over <= 1'b1;
                               end
                            else
                               begin
                                  stack_wrena <= 1'b1;
                                  stack_addra <= stack_addra + 1'b1;
											 push_pc <= next_pc;
                                  pc <= (callsxsy == 1'b1)?{sx_dout[3:0],sx_dout[7:0]}:inst_embed_addr;
                               end
                         end
                  3'b010:begin
                            if(stack_addra == 6'h3f)// under flow
                               begin
                                  stack_pointer_over <= 1'b1;
                               end
                            else
                               begin
                                  stack_addra <= stack_addra - 1'b1;
                                  pc <= pop_pc;
                               end
                         end
                  3'b001:begin
                            pc <= (jumpsxsy == 1'b1)?{sx_dout[3:0],sx_dout[7:0]}:inst_embed_addr;
                         end
                  default:begin // push_stack,pop_stack,jump_cmd are not interrupted by internal_int
                            case({ena_ie,dis_ie})
                               2'b10:ie_flag <= 1'b1;
                               2'b01:ie_flag <= 1'b0;
                               default:ie_flag <= ie_flag;
                            endcase
                            case({internal_int&ie_flag & (~isp_runing),(reti_dis_intr|reti_ena_intr) & isp_runing})
                                2'b10:begin
                                         pc <= interrupt_vector;
                                         internal_int_ack <= 1'b1;
                                         isp_runing <= 1'b1;
                                         interrupt_pc_stack <= next_pc;
                                      end
                                2'b01:begin
                                         pc <= interrupt_pc_stack;
                                         reti_pop <= 1'b1;
                                         isp_runing <= 1'b0;
                                      end
                                default:begin
                                         pc <= next_pc;
                                      end
                            endcase
                         end
              endcase
           end
        else
           begin
              stack_wrena <= 1'b0;
              internal_int_ack <= 1'b0;
              reti_pop <= 1'b0;
           end
      end
end
always@(posedge clk)
begin
   if(internal_reset == 1'b1 || (stack_pointer_over) == 1'b1)
	   begin
		   {reti_bank,reti_z_flag,reti_c_flag} <= 3'b000;
			internal_int_ack_d1 <= 1'b0;
		end
   else
	   begin
		   internal_int_ack_d1 <= internal_int_ack;
			if(internal_int_ack_d1 == 1'b1)
			   begin
		         {reti_bank,reti_z_flag,reti_c_flag} <= {bank,z_flag,c_flag};
			   end
		end
end

endmodule


//////////////////////////////////////////////////////
module ramnx8 #(
   parameter integer scratch_pad_memory_size = 5, //2^scratch_pad_memory_size
   parameter integer scratch_pad_memory_width = 8
   )
(
   input clka,  
	input[scratch_pad_memory_size-1:0] addra,
   input wrena,
   input[scratch_pad_memory_width-1:0] dina,
   input[scratch_pad_memory_size-1:0] addrb,
   output[scratch_pad_memory_width-1:0] doutb
   );
reg[scratch_pad_memory_width-1:0] scram[0:(2**scratch_pad_memory_size-1)];
integer i;
initial
   for(i=0;i<2**scratch_pad_memory_size;i=i+1)
	    scram[i] = 8'd0;
/////////////////////////////////////////////////		 
assign doutb = scram[addrb];
always@(posedge clka)
begin
  if(wrena == 1'b1)
	  begin
        scram[addra] <= dina;
	  end
end
endmodule
////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////
module szmp8_alu#(
   parameter integer scratch_pad_memory_size = 6,//2^scratch_pad_memory_size
   parameter [7:0] 	hwbuild_parameter = 8'h00

 )
(
   input clk,
   input rst,
   input t_state_d1,
   input t_state_d2,
   input sy_const,// 0 for sy, 1 for kk or pp or ss 
   input cy_flag,// for add addcy sub subcy compare comparecy test testcy,0 for add or sub or compare or test, 1 for addcy or subcy or comparecy or testcy
   input load,
   input star,
   input ands,
   input ors,
   input xors,
   input add,
   input sub,
   input test,
   input compare,
   input sl0,
   input sl1,
   input slx,
   input sla,
   input rl,
   input sr0,
   input sr1,
   input srx,
   input sra,
   input rr,
   input load_ret,
   input hwbd,
	input regbanka,
   input regbankb,
   
   input inputsp,
   input outputsp,
   input outputk,
   input fetch,
   input store,

   input[7:0] in_port,
   output reg [7:0] out_port,
   output[7:0] port_id,
   output reg write_strobe,
   output reg k_write_strobe,
   output read_strobe,
	
	input reti_pop,//drive by t_state_d1
	input reti_bank,
	input reti_c_flag,
	input reti_z_flag,
	
   input[3:0] sx_ain,
   input[7:0] sx_din,
   input[7:0] sy_din,
   input[11:0] kk,
   output reg sreg_bank = 1'b0,
   output c_flag_out,
   output z_flag_out,
   output[4:0] sx_aout,//bit4 
   output sx_wren,
   output reg[7:0] sx_dout
);
///////////////////////////////////
reg c_flag = 1'b0,z_flag = 1'b0;
wire[scratch_pad_memory_size-1:0] spm_addr;
wire[7:0] spm_dout,spm_din;
wire spm_wren;
wire test_c_flag;
wire[7:0] operate_b;
reg[7:0] and_out,or_out,xor_out;
reg[8:0] addcy_out,subcy_out;// bit8 c flag
reg[7:0] load_and_star_out;
reg l_shift_bit,r_shift_bit;
reg[8:0] l_shift_out,r_shift_out;// l_shift[8] = c,r_shift[0]=c
reg[7:0] load_ret_out;
reg load_inst,and_inst,or_inst,xor_inst,add_inst,sub_inst,l_shift_inst,r_shift_inst,hwbd_inst,input_inst;
reg star_inst,test_inst,cmp_inst,fetch_inst,store_inst;
reg[3:0] sx_ain_d1;
reg cy_flag_d1;
wire flag_update;
wire and_z_flag,or_z_flag,xor_z_flag,add_z_flag,sub_z_flag,l_shift_z_flag,r_shift_z_flag,hwbd_z_flag;
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

ramnx8 #(
   .scratch_pad_memory_size(scratch_pad_memory_size), //6,7,8
   .scratch_pad_memory_width(8)
   )
ramnx8_spm  
(
   .clka(clk),
   .addra(spm_addr),
   .wrena(spm_wren),
   .dina(spm_din),
   .addrb(spm_addr),
   .doutb(spm_dout)
   );
//////////////////////////////////////////
// state_d1 



assign  operate_b = (sy_const == 1'b0) ? sy_din : kk[7:0];
always@(sl0,sl1,slx,sla,rl,c_flag,sx_din)
begin
   case({sl0,sl1,slx,sla,rl})
       5'b01000:l_shift_bit = 1'b1;
       5'b00100:l_shift_bit = sx_din[0];
       5'b00010:l_shift_bit = c_flag;
       5'b00001:l_shift_bit = sx_din[7];
       default:l_shift_bit = 1'b0;//5'b10000:
   endcase
end
always@(sr0,sr1,srx,sra,rr,c_flag,sx_din)
begin
   case({sr0,sr1,srx,sra,rr})
       5'b01000:r_shift_bit = 1'b1;
       5'b00100:r_shift_bit = sx_din[7];
       5'b00010:r_shift_bit = c_flag;
       5'b00001:r_shift_bit = sx_din[0];
       default:r_shift_bit = 1'b0;//5'b10000:
   endcase
end


always@(posedge clk)
begin
   if(t_state_d1 == 1'b1)
      begin
         load_and_star_out <= operate_b;//for load,star,load&return
         and_out <= sx_din & operate_b;// for and,test
         or_out  <= sx_din | operate_b;
         xor_out  <= sx_din ^ operate_b;
         addcy_out <= {1'b0,sx_din} + operate_b + (c_flag&cy_flag);
         subcy_out <= {1'b0,sx_din} - operate_b - (c_flag&cy_flag);
         l_shift_out <= {sx_din,l_shift_bit};
         r_shift_out <= {r_shift_bit,sx_din}; 
         /////////////////
         // no change
         fetch_inst <= fetch;
         store_inst <= store;
         input_inst <= inputsp;
         load_inst <= load|load_ret|star;
         star_inst <= star;
         and_inst <= ands;
         test_inst <= test;
         or_inst <= ors;
         xor_inst <= xors;
         add_inst <= add;
         sub_inst <= sub;
         l_shift_inst <= sl0|sl1|slx|sla|rl;
         r_shift_inst <= sr0|sr1|srx|sra|rr;
         cmp_inst <= compare;
         hwbd_inst <= hwbd;
         sx_ain_d1 <= sx_ain;
         cy_flag_d1 <= cy_flag;
         //////////////////////////
         
      end
end


always@(posedge clk)
begin
   if(rst== 1'b1)
      begin
         sreg_bank <= 1'b0;
      end
   else
      begin
		   if(t_state_d2 == 1'b1)
            begin
				   case({reti_pop,regbanka,regbankb})
					    3'b100:sreg_bank <= reti_bank;
                   3'b010:sreg_bank <= 1'b0;
                   3'b001:sreg_bank <= 1'b1;
                   default:sreg_bank <= sreg_bank;
               endcase
				end
         
      end
end

////////////////////////////////////////////////////////////////////////
// t_state_d2   c z flag
assign test_c_flag = ^{and_out,(c_flag&cy_flag_d1)};
assign flag_update = hwbd|r_shift_inst|l_shift_inst|add_inst|sub_inst|test_inst|cmp_inst|and_inst|or_inst|xor_inst;
assign and_z_flag = (and_out == 8'h00) ? and_inst|(test_inst&(~cy_flag_d1))|(test_inst&cy_flag_d1&z_flag):1'b0;
assign or_z_flag = (or_out == 8'h00) ? or_inst : 1'b0;
assign xor_z_flag = (xor_out == 8'h00) ? xor_inst : 1'b0;
assign add_z_flag = (addcy_out[7:0] == 8'h00) ? (add_inst&(~cy_flag_d1))|(add_inst&cy_flag_d1&z_flag) : 1'b0;
assign sub_z_flag = (subcy_out[7:0] == 8'h00) ? (sub_inst&(~cy_flag_d1))|(sub_inst&cy_flag_d1&z_flag)|(cmp_inst&(~cy_flag_d1))|(cmp_inst&cy_flag_d1&z_flag) : 1'b0;
assign l_shift_z_flag = (l_shift_out[7:0] == 8'h00) ? l_shift_inst : 1'b0;
assign r_shift_z_flag = (r_shift_out[8:1] == 8'h00) ? r_shift_inst : 1'b0;
assign hwbd_z_flag = (hwbuild_parameter == 8'h00) ? hwbd_inst : 1'b0;

assign c_flag_out = c_flag;
assign z_flag_out = z_flag;


always@(posedge clk)
begin
   if(rst == 1'b1)
      begin
         c_flag <= 1'b0;
         z_flag <= 1'b0;
      end
   else
      begin
         if(t_state_d2 == 1'b1)
            begin
				   case({flag_update,reti_pop})
					    2'b10:begin
						          c_flag <= hwbd|(r_shift_out[0]&r_shift_inst)|(l_shift_out[8]&l_shift_inst)|(addcy_out[8]&add_inst)|(subcy_out[8]&(sub_inst|cmp_inst))|(test_c_flag&test_inst);
                            z_flag <= and_z_flag|or_z_flag|xor_z_flag|add_z_flag|sub_z_flag|l_shift_z_flag|r_shift_z_flag|hwbd_z_flag;
						       end
						 2'b01:begin
						          c_flag <= reti_c_flag;
                            z_flag <= reti_z_flag;
						       end
						 default:begin
						          c_flag <= c_flag;
                            z_flag <= c_flag;
						       end
					endcase
            end
      end
end 
///////////////////////////////////////////
// sx out

always@(*)
begin
   case({fetch_inst,input_inst,load_inst,and_inst,or_inst,xor_inst,add_inst,sub_inst,l_shift_inst,r_shift_inst,hwbd_inst})
       11'h400:sx_dout = spm_dout;
       11'h200:sx_dout = in_port;
       11'h100:sx_dout = load_and_star_out;
       11'h080:sx_dout = and_out;
       11'h040:sx_dout = or_out;
       11'h020:sx_dout = xor_out;
       11'h010:sx_dout = addcy_out[7:0];
       11'h008:sx_dout = subcy_out[7:0];
       11'h004:sx_dout = l_shift_out[7:0];
       11'h002:sx_dout = r_shift_out[8:1];
       11'h001:sx_dout = hwbuild_parameter;
       default:sx_dout = 8'h00;
   endcase
end
assign sx_wren = (fetch_inst|input_inst|load_inst|and_inst|or_inst|xor_inst|add_inst|sub_inst|l_shift_inst|r_shift_inst|hwbd_inst)&t_state_d2;
assign sx_aout = {sreg_bank^star_inst,sx_ain_d1};
/////////////////////////////////////////////////
// io controll
////////////////////
//input
assign read_strobe = t_state_d1 & inputsp;
assign port_id = (outputk == 1'b1) ? {4'h0,kk[3:0]} : ((sy_const == 1'b0) ? sy_din : kk[7:0]);
always@(posedge clk)
begin
   out_port <= (outputk == 1'b1) ? kk[11:4]:sx_din;
   write_strobe <= outputsp & t_state_d1;
   k_write_strobe <= outputk & t_state_d1;
end
////////////////////////////////////
//fetch,store
assign spm_addr = operate_b[scratch_pad_memory_size-1:0];
assign spm_din = sx_din;
assign spm_wren = t_state_d2&store_inst;
/////////////////////////////////////
endmodule

////////////////////////////////////////////
module szmp8_dec(
   input[17:0] instruction,
   output sy_const,// 0 for sy, 1 for kk or pp or ss 
   output cy_flag,// for add addcy sub subcy compare comparecy test testcy,0 for add or sub or compare or test, 1 for addcy or subcy or comparecy or testcy
   output load,
   output star,
   output ands,
   output ors,
   output xors,
   output add,
   output sub,
   output test,
   output compare,
   output sl0,
   output sl1,
   output slx,
   output sla,
   output rl,
   output sr0,
   output sr1,
   output srx,
   output sra,
   output rr,
   output regbanka,
   output regbankb,
   output inputsp,
   output outputsp,
   output outputk,
   output store,
   output fetch,
   output dis_intr,
   output ena_intr,
   output reti_dis_intr,
   output reti_ena_intr,
   output jump,
   output jumpz,
   output jumpnz,
   output jumpc,
   output jumpnc,
   output jumpsxsy,
   output call,
   output callz,
   output callnz,
   output callc,
   output callnc,
   output callsxsy,
   output ret,
   output retz,
   output retnz,
   output retc,
   output retnc,
   output load_ret,
   output hwbd,    //hwbuild
   output[11:0] inst_embed_addr,// address that in instruction
   output[3:0] sx,
   output[3:0] sy,
   output[11:0] kk // normal kk[7:0] is used, for outputk,kk[11:4]is constant kk[3:0] is port
   );
//////////////////////////////////////
wire shift_rotate;
///////////////////////////////
assign sy_const = instruction[12];
assign cy_flag = instruction[13];
assign load = (instruction[17:13]== 5'b00000) ? 1'b1 : 1'b0;
assign star = (instruction[17:13]== 5'b01011) ? 1'b1 : 1'b0;
assign ands = (instruction[17:13]== 5'b00001) ? 1'b1 : 1'b0;
assign ors = (instruction[17:13]== 5'b00010) ? 1'b1 : 1'b0;
assign xors = (instruction[17:13]== 5'b00011) ? 1'b1 : 1'b0;
assign add = (instruction[17:14]== 4'b0100) ? 1'b1 : 1'b0;
assign sub = (instruction[17:14]== 4'b0110) ? 1'b1 : 1'b0;
assign test = (instruction[17:14]== 4'b0011) ? 1'b1 : 1'b0;
assign compare = (instruction[17:14]== 4'b0111) ? 1'b1 : 1'b0;


assign shift_rotate = ({instruction[17:12],instruction[7]} == 7'b0101000) ? 1'b1 : 1'b0;
assign sl0 = ({shift_rotate,instruction[3:0]} == 5'b10110) ? 1'b1 : 1'b0;
assign sl1 = ({shift_rotate,instruction[3:0]} == 5'b10111) ? 1'b1 : 1'b0;
assign slx = ({shift_rotate,instruction[3:0]} == 5'b10100) ? 1'b1 : 1'b0;
assign sla = ({shift_rotate,instruction[3:0]} == 5'b10000) ? 1'b1 : 1'b0;
assign rl = ({shift_rotate,instruction[3:0]} == 5'b10010) ? 1'b1 : 1'b0;
assign sr0 = ({shift_rotate,instruction[3:0]} == 5'b11110) ? 1'b1 : 1'b0;
assign sr1 = ({shift_rotate,instruction[3:0]} == 5'b11111) ? 1'b1 : 1'b0;
assign srx = ({shift_rotate,instruction[3:0]} == 5'b11010) ? 1'b1 : 1'b0;
assign sra = ({shift_rotate,instruction[3:0]} == 5'b11000) ? 1'b1 : 1'b0;
assign rr = ({shift_rotate,instruction[3:0]} == 5'b11100) ? 1'b1 : 1'b0;

assign regbanka = ({instruction[17:12],instruction[0]}== 7'b1101110) ? 1'b1 : 1'b0;
assign regbankb = ({instruction[17:12],instruction[0]}== 7'b1101111) ? 1'b1 : 1'b0;

assign inputsp = (instruction[17:13]== 5'b00100) ? 1'b1 : 1'b0;
assign outputsp = (instruction[17:13]== 5'b10110) ? 1'b1 : 1'b0;
assign outputk = (instruction[17:12]== 6'b101011) ? 1'b1 : 1'b0;
assign store = (instruction[17:13]== 5'b10111) ? 1'b1 : 1'b0;
assign fetch = (instruction[17:13]== 5'b00101) ? 1'b1 : 1'b0;


assign dis_intr = ({instruction[17:12],instruction[0]}== 7'b1010000) ? 1'b1 : 1'b0;
assign ena_intr = ({instruction[17:12],instruction[0]}== 7'b1010001) ? 1'b1 : 1'b0;

assign reti_dis_intr = ({instruction[17:12],instruction[0]}== 7'b1010010) ? 1'b1 : 1'b0;
assign reti_ena_intr = ({instruction[17:12],instruction[0]}== 7'b1010011) ? 1'b1 : 1'b0;
assign jump = (instruction[17:12]== 6'b100010) ? 1'b1 : 1'b0;
assign jumpz = (instruction[17:12]== 6'b110010) ? 1'b1 : 1'b0;
assign jumpnz = (instruction[17:12]== 6'b110110) ? 1'b1 : 1'b0;
assign jumpc = (instruction[17:12]== 6'b111010) ? 1'b1 : 1'b0;
assign jumpnc = (instruction[17:12]== 6'b111110) ? 1'b1 : 1'b0;
assign jumpsxsy = (instruction[17:12]== 6'b100110) ? 1'b1 : 1'b0;
assign call = (instruction[17:12]== 6'b100000) ? 1'b1 : 1'b0;
assign callz = (instruction[17:12]== 6'b110000) ? 1'b1 : 1'b0;
assign callnz = (instruction[17:12]== 6'b110100) ? 1'b1 : 1'b0;
assign callc = (instruction[17:12]== 6'b111000) ? 1'b1 : 1'b0;
assign callnc = (instruction[17:12]== 6'b111100) ? 1'b1 : 1'b0;
assign callsxsy = (instruction[17:12]== 6'b100100) ? 1'b1 : 1'b0;
assign ret = (instruction[17:12]== 6'b100101) ? 1'b1 : 1'b0;
assign retz = (instruction[17:12]== 6'b110001) ? 1'b1 : 1'b0;
assign retnz = (instruction[17:12]== 6'b110101) ? 1'b1 : 1'b0;
assign retc = (instruction[17:12]== 6'b111001) ? 1'b1 : 1'b0;
assign retnc = (instruction[17:12]== 6'b111101) ? 1'b1 : 1'b0;
assign load_ret = (instruction[17:12]== 6'b100001) ? 1'b1 : 1'b0;

assign hwbd = ({instruction[17:12],instruction[7]}== 7'b0101001) ? 1'b1 : 1'b0;
assign inst_embed_addr = instruction[11:0];
assign sx = instruction[11:8];
assign sy = instruction[7:4];
assign kk = instruction[11:0];
endmodule
