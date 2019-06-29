// Credits to:
// https://github.com/jbush001/NyuziProcessor/blob/master/hardware/fpga/common/async_fifo.sv
// https://github.com/ZipCPU/website/blob/master/examples/afifo.v
//
// Copyright 2011-2015 Jeff Bush
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//
// Asynchronous FIFO, with two clock domains
// reset is asynchronous and is synchronized to each clock domain
// internally.
// NUM_ENTRIES must be a power of two and >= 2
//

`default_nettype none

module async_fifo
    #(parameter WIDTH = 32,
    parameter NUM_ENTRIES = 8)

    (input                  write_reset,
     input					read_reset,

    // Read.
    input                   read_clk,
    input                   read_en,
    output [WIDTH - 1:0]    read_data,
    output logic            empty,

    // Write
    input                   write_clk,
    input                   write_en,
    output logic            full,
    input [WIDTH - 1:0]     write_data);

    localparam ADDR_WIDTH = $clog2(NUM_ENTRIES);

    logic[ADDR_WIDTH - 1:0] write_ptr_sync;
    logic[ADDR_WIDTH - 1:0] read_ptr;
    logic[ADDR_WIDTH - 1:0] read_ptr_gray;
    logic[ADDR_WIDTH - 1:0] read_ptr_nxt;
    logic[ADDR_WIDTH - 1:0] read_ptr_gray_nxt;
    logic reset_rsync;
    logic[ADDR_WIDTH - 1:0] read_ptr_sync;
    logic[ADDR_WIDTH - 1:0] write_ptr;
    logic[ADDR_WIDTH - 1:0] write_ptr_gray;
    logic[ADDR_WIDTH - 1:0] write_ptr_nxt;
    logic[ADDR_WIDTH - 1:0] write_ptr_gray_nxt;
    logic reset_wsync;
    logic [WIDTH - 1:0] fifo_data[0:NUM_ENTRIES - 1];

    assign read_ptr_nxt = read_ptr + 1;
    assign read_ptr_gray_nxt = read_ptr_nxt ^ (read_ptr_nxt >> 1);
    assign write_ptr_nxt = write_ptr + 1;
    assign write_ptr_gray_nxt = write_ptr_nxt ^ (write_ptr_nxt >> 1);

    //
    // Read clock domain
    //
    synchronizer #(.WIDTH(ADDR_WIDTH)) write_ptr_synchronizer(
        .clk(read_clk),
        .reset(reset_rsync),
        .data_o(write_ptr_sync),
        .data_i(write_ptr_gray));

    assign empty = write_ptr_sync == read_ptr_gray;

	// For further info on reset synchronizer, see 
	// https://www.youtube.com/watch?v=mYSEVdUPvD8 and
	// http://zipcpu.com/formal/2018/04/12/areset.html

    synchronizer #(.RESET_STATE(1)) read_reset_synchronizer(
        .clk(read_clk),
        .reset(read_reset),
        .data_i(0),
        .data_o(reset_rsync));

    always_ff @(posedge read_clk, posedge reset_rsync)
    begin
        if (reset_rsync)
        begin
            /*AUTORESET*/
            // Beginning of autoreset for uninitialized flops
            read_ptr <= 0;
            read_ptr_gray <= 0;
            // End of automatics
        end
        else if (read_en && !empty)
        begin
            read_ptr <= read_ptr_nxt;
            read_ptr_gray <= read_ptr_gray_nxt;
        end
    end

    assign read_data = fifo_data[read_ptr];

    //
    // Write clock domain
    //
    synchronizer #(.WIDTH(ADDR_WIDTH)) read_ptr_synchronizer(
        .clk(write_clk),
        .reset(reset_wsync),
        .data_o(read_ptr_sync),
        .data_i(read_ptr_gray));

    assign full = write_ptr_gray_nxt == read_ptr_sync;

    synchronizer #(.RESET_STATE(1)) write_reset_synchronizer(
        .clk(write_clk),
        .reset(write_reset),
        .data_i(0),
        .data_o(reset_wsync));

	integer i;

    always_ff @(posedge write_clk, posedge reset_wsync)
    begin
        if (reset_wsync)
        begin
            //`ifdef NEVER
            for (i=0; i<NUM_ENTRIES; i++)
			begin
				fifo_data[i] <= {WIDTH{1'b0}}; // Suppress autoreset
			end    
            //`endif

            /*AUTORESET*/
            // Beginning of autoreset for uninitialized flops
            write_ptr <= 0;
            write_ptr_gray <= 0;
            // End of automatics
        end
        else if (write_en && !full)
        begin
            fifo_data[write_ptr] <= write_data;
            write_ptr <= write_ptr_nxt;
            write_ptr_gray <= write_ptr_gray_nxt;
        end
    end

/*See https://zipcpu.com/blog/2018/07/06/afifo.html for a formal proof of afifo in general*/

`ifdef FORMAL

	reg first_clock_had_passed;
	reg first_write_clock_had_passed;
	reg first_read_clock_had_passed;

	initial first_clock_had_passed = 0;
	initial first_write_clock_had_passed = 0;
	initial first_read_clock_had_passed = 0;

	always_ff @($global_clock)
		first_clock_had_passed <= 1;	

	always_ff @(posedge write_clk)
		first_write_clock_had_passed <= 1;

	always_ff @(posedge read_clk)
		first_read_clock_had_passed <= 1;

	//always @($global_clock)
		//assert($rose(reset_wsync)==$rose(reset_rsync));  // comment this out for experiment

	initial assume(write_reset);
	initial assume(read_reset);
	initial assert(empty);
	initial assert(!full);
	
	always_ff @($global_clock)
	begin
		if(reset_wsync)
		begin
			assert(write_ptr == 0);
			assert(write_ptr_gray == 0);
			assert(!full);
		end

		else if(first_write_clock_had_passed) 
		begin

		end
	end

	always_ff @($global_clock)
	begin
		if(reset_rsync)
		begin
			assert(read_ptr == 0);
			assert(read_ptr_gray == 0);
			assert(empty);
		end

		else if(first_read_clock_had_passed) 
		begin

		end
	end

	always_ff @($global_clock)
	begin
		if (first_clock_had_passed)
		begin
			if(reset_wsync)
			begin
				assert(!full);		
				assert(read_data == 0);
			end

			else if (!$rose(write_clk))
			begin
				assume($stable(write_en));
				assume($stable(write_data));
				assert($stable(full));
			end		
			
			if(reset_rsync)
				assert(empty);		

			else if (!$rose(read_clk))
			begin
				assume($stable(read_en));
				assert($stable(empty));
				if(!reset_wsync && !$rose(write_clk) && !write_en) assert($stable(read_data));				
			end						
		end
	end
`endif

/*The following is a fractional clock divider code*/

`ifdef FORMAL

	/*
	if f_wclk_step and f_rclk_step have different value, how do the code guarantee that it will still generate two different clocks, both with 50% duty cycle ?
	This is a fundamental oscillator generation technique.
	Imagine a table, indexed from 0 to 2^N-1, filled with a square wave
	If you stepped through that table one at a time, and did a lookup, the output would be a square wave
	If you stepped through it two at a time--same thing
	Indeed, you might imagine the square wave going on for infinity as the table replicates itself time after time, and that the N bits used to index it are only the bottom N--the top bits index which table--but they become irrelevant since we are only looking for a repeating waveform
	Hence, no matter how fast you step as long as it is less than 2^(N-1), you'll always get a square wave

	http://zipcpu.com/blog/2017/06/02/generating-timing.html
	http://zipcpu.com/dsp/2017/07/11/simplest-sinewave-generator.html
	http://zipcpu.com/dsp/2017/12/09/nco.html
	*/	

	localparam	F_CLKBITS=5;
	wire	[F_CLKBITS-1:0]	f_wclk_step, f_rclk_step;

	assign	f_wclk_step = $anyconst;
	assign	f_rclk_step = $anyconst;

	always @(*)
		assume(f_wclk_step != 0);
	always @(*)
		assume(f_rclk_step != 0);
	always @(*)
		assume(f_rclk_step != f_wclk_step); // so that we have two different clock speed
		
	reg	[F_CLKBITS-1:0]	f_wclk_count, f_rclk_count;

	always @($global_clock)
		f_wclk_count <= f_wclk_count + f_wclk_step;
	always @($global_clock)
		f_rclk_count <= f_rclk_count + f_rclk_step;

	always @(*)
	begin
		assume(write_clk == gclk_w);
		assume(read_clk == gclk_r);
		cover(write_clk);
		cover(read_clk);
	end

	wire gclk_w, gclk_r;
	wire enable_in_w, enable_in_r;

	assign enable_in_w = $anyseq;
	assign enable_in_r = $anyseq;

	clock_gate cg_w (.gclk(gclk_w), .clk(f_wclk_count[F_CLKBITS-1]), .enable_in(enable_in_w));

	clock_gate cg_r (.gclk(gclk_r), .clk(f_rclk_count[F_CLKBITS-1]), .enable_in(enable_in_r));

`endif

`ifdef FORMAL

	////////////////////////////////////////////////////
	//
	// Some cover statements, to make sure valuable states
	// are even reachable
	//
	////////////////////////////////////////////////////
	//

	// Make sure a reset is possible in either domain
	always_ff @(posedge write_clk)
		cover(write_reset);

	always_ff @(posedge read_clk)
		cover(read_reset);


	always_ff @($global_clock)
	if (first_clock_had_passed)
		cover((empty)&&(!$past(empty)));

	always @(*)
	if (first_clock_had_passed)
		cover(full);

	always_ff @(posedge write_clk)
	if (first_write_clock_had_passed)
		cover($past(full)&&($past(write_en))&&(full));

	always_ff @(posedge write_clk)
	if (first_write_clock_had_passed)
		cover($past(full)&&(!full));

	always_ff @(posedge write_clk)
		cover((full)&&(write_en));

	always_ff @(posedge write_clk)
		cover(write_en);

	always_ff @(posedge read_clk)
		cover((empty)&&(read_en));

	always_ff @(posedge read_clk)
	if (first_read_clock_had_passed)
		cover($past(!empty)&&($past(read_en))&&(empty));
		
`endif
	
`ifdef FORMAL
	
	/* twin-write test */
	// write two pieces of different data into the asynchronous fifo
	// then read them back from the asynchronous fifo
	
	wire [WIDTH - 1:0] first_data;
	wire [WIDTH - 1:0] second_data;
	
	assign first_data = $anyconst;
	assign second_data = $anyconst;
	
	reg first_data_is_written;
	reg first_data_is_read;
	reg second_data_is_written;
	reg second_data_is_read;
	
	initial first_data_is_read = 0;
	initial second_data_is_read = 0;
	initial first_data_is_written = 0;
	initial second_data_is_written = 0;
	
	//always @(*) assume(write_reset == read_reset);
	always @(*) assume(first_data != 0);
	always @(*) assume(second_data != 0);
	always @(*) assume(first_data != second_data);
	
	always_ff @(posedge write_clk)
	begin
		if(reset_wsync)
		begin
			first_data_is_written <= 0;
			second_data_is_written <= 0;
		end
	
		else if(write_en && !$past(first_data_is_written))
		begin
			assume(write_data == first_data);
			first_data_is_written <= 1;	
		end
		
		else if(write_en && first_data_is_written && !$past(second_data_is_written))
		begin
			assume(write_data == second_data);
			second_data_is_written <= 1;	
		end
	end

	reg [WIDTH - 1:0] first_data_read_out;
	reg [WIDTH - 1:0] second_data_read_out;
	
	initial first_data_read_out = 0;
	initial second_data_read_out = 0;

	always_ff @(posedge read_clk)
	begin
		if(reset_rsync)
		begin  
			first_data_read_out <= 0;
			second_data_read_out <= 0;
			first_data_is_read <= 0;
			second_data_is_read <= 0;
		end
	
		else if(read_en && first_data_is_written && !first_data_is_read)
		begin
			first_data_read_out <= read_data;
			first_data_is_read <= 1;	
		end
		
		else if(read_en && second_data_is_written && !second_data_is_read)
		begin
			second_data_read_out <= read_data;
			second_data_is_read <= 1;	
		end
	end

	reg past_reset_rsync; 
	always @(posedge read_clk) past_reset_rsync <= reset_rsync; // to emulate $past(reset_rsync)

	always @(*)
	begin
		if(first_read_clock_had_passed && past_reset_rsync)
		begin  
			assert(first_data_read_out == 0);
			assert(second_data_read_out == 0);
		end

		else begin

			if(first_data_is_read) 
			begin
				cover(first_data_read_out == first_data);
				assert(first_data_read_out == first_data);
			end
			
			if(second_data_is_read)
			begin
				cover(second_data_read_out == second_data);
				assert(second_data_read_out == second_data);
			end
		end
	end

`endif

endmodule
