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

// for writing and reading 2 different values into 2 different FIFO entry locations
`define ENABLE_TWIN_WRITE_TEST 1

module async_fifo
    #(
    	`ifdef FORMAL
			parameter WIDTH = 4,
		`else
			parameter WIDTH = 32,		
		`endif
		
		parameter NUM_ENTRIES = 8
    )

    (input                  write_reset,
     input					read_reset,

    // Read.
    input                   read_clk,
    input                   read_en,
    output [WIDTH - 1:0]    read_data,
    output 		            empty,

    // Write
    input                   write_clk,
    input                   write_en,
    output		            full,
    input [WIDTH - 1:0]     write_data);

    localparam ADDR_WIDTH = $clog2(NUM_ENTRIES);

    wire [ADDR_WIDTH:0] write_ptr_sync;
    reg  [ADDR_WIDTH:0] read_ptr;
    reg  [ADDR_WIDTH:0] read_ptr_gray;
    wire [ADDR_WIDTH:0] read_ptr_nxt;
    wire [ADDR_WIDTH:0] read_ptr_gray_nxt;
    wire reset_rsync;
    wire [ADDR_WIDTH:0] read_ptr_sync;
    reg  [ADDR_WIDTH:0] write_ptr;
    reg  [ADDR_WIDTH:0] write_ptr_gray;
    wire [ADDR_WIDTH:0] write_ptr_nxt;
    wire [ADDR_WIDTH:0] write_ptr_gray_nxt;
    wire reset_wsync;
    reg [WIDTH - 1:0] fifo_data[0:NUM_ENTRIES - 1];

    assign read_ptr_nxt = read_ptr + 1;
    assign read_ptr_gray_nxt = read_ptr_nxt ^ (read_ptr_nxt >> 1);
    assign write_ptr_nxt = write_ptr + 1;
    assign write_ptr_gray_nxt = write_ptr_nxt ^ (write_ptr_nxt >> 1);

    //
    // Read clock domain
    //
    synchronizer #(.WIDTH(ADDR_WIDTH+1)) write_ptr_synchronizer(
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
        .data_i(1'b0),
        .data_o(reset_rsync));

    always @(posedge read_clk)
    begin
        if (reset_rsync)
        begin
            read_ptr <= 0;
            read_ptr_gray <= 0;
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
    synchronizer #(.WIDTH(ADDR_WIDTH+1)) read_ptr_synchronizer(
        .clk(write_clk),
        .reset(reset_wsync),
        .data_o(read_ptr_sync),
        .data_i(read_ptr_gray));

	reg [ADDR_WIDTH:0] full_check;
    always @(posedge write_clk) 
    begin
    	if(full) full_check <= write_ptr_gray ^ read_ptr_sync;
    	
    	else full_check <= write_ptr_gray_nxt ^ read_ptr_sync;
    end

	// See https://electronics.stackexchange.com/questions/596233/address-rollover-for-asynchronous-fifo    	
    assign full = (full_check[ADDR_WIDTH] & full_check[ADDR_WIDTH-1]) && (full_check[0 +: (ADDR_WIDTH-1)] == 0);

    synchronizer #(.RESET_STATE(1)) write_reset_synchronizer(
        .clk(write_clk),
        .reset(write_reset),
        .data_i(1'b0),
        .data_o(reset_wsync));

	integer i;

    always @(posedge write_clk)
    begin
        if (reset_wsync)
        begin
            `ifdef FORMAL
		        for (i=0; i<NUM_ENTRIES; i++)
				begin
					fifo_data[i] <= {WIDTH{1'b0}};
				end    
            `endif

            write_ptr <= 0;
            write_ptr_gray <= 0;
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

	always @($global_clock)
		first_clock_had_passed <= 1;	

	always @(posedge write_clk)
		first_write_clock_had_passed <= 1;

	always @(posedge read_clk)
		first_read_clock_had_passed <= 1;

	//always @($global_clock)
		//assert($rose(reset_wsync)==$rose(reset_rsync));  // comment this out for experiment

	initial assume(write_reset);
	initial assume(read_reset);
	initial assume(empty);
	initial assume(!full);

	reg reset_rsync_is_done;
	initial reset_rsync_is_done = 0;
	initial assert(reset_rsync == 0);	

    always @(posedge read_clk)
    begin
    	if (read_reset) reset_rsync_is_done <= 0;
    
        else if (reset_rsync) reset_rsync_is_done <= 1;
    end

	reg reset_wsync_is_done;
	initial reset_wsync_is_done = 0;	
	initial assert(reset_wsync == 0);	

    always @(posedge write_clk)
    begin
    	if (write_reset) reset_wsync_is_done <= 0;
    
        else if (reset_wsync) reset_wsync_is_done <= 1;
    end
    
	always @($global_clock)
	begin
		if (first_clock_had_passed)
		begin
			if($past(reset_wsync) && ($rose(write_clk)))
			begin
				assert(write_ptr == 0);
				assert(write_ptr_gray == 0);
				assert(read_data == 0);
			end

			else if (!$rose(write_clk))
			begin
				assume($stable(write_reset));
				assume($stable(write_en));
				assume($stable(write_data));
			end		
			
			if($past(reset_rsync) && ($rose(read_clk)))
			begin
				assert(read_ptr == 0);
				assert(read_ptr_gray == 0);
				assert(empty);
			end	

			else if (!$rose(read_clk))
			begin
				assume($stable(read_reset));
				assume($stable(read_en));
				assert(empty == (write_ptr_sync == read_ptr_gray));
				
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
	
	always @(*) assume(first_data > NUM_ENTRIES);
	always @(*) assume(second_data > NUM_ENTRIES);
	always @(*) assume(first_data != second_data);

	reg [ADDR_WIDTH:0] first_address;
	reg [ADDR_WIDTH:0] second_address;
	
	always @(posedge write_clk) assume(first_address != second_address);
	
	always @(posedge write_clk)
	begin
		if(reset_wsync)
		begin
			first_data_is_written <= 0;
			second_data_is_written <= 0;
		end
	
		else if(write_en && !full && !first_data_is_written)
		begin
			assume(write_data == first_data);
			first_data_is_written <= 1;	
			first_address <= write_ptr;
		end
		
		else if(write_en && !full && !second_data_is_written)
		begin
			assume(write_data == second_data);
			second_data_is_written <= 1;
			second_address <= write_ptr;	
		end
	end

	always @($global_clock)
	begin
		if(first_clock_had_passed && ($rose(write_clk)))
		begin
			if($past(reset_wsync))
			begin
				assert(first_data_is_written == 0);
				assert(second_data_is_written == 0);
			end
		
			else if($past(write_en) && !$past(full) && !$past(first_data_is_written))
			begin
				assert(first_data_is_written == 1);	
				assert(first_address == $past(write_ptr));
				assert($past(first_data) == fifo_data[first_address]);
			end
			
			else if($past(write_en) && !$past(full) && !$past(second_data_is_written))
			begin
				assert(second_data_is_written == 1);
				assert(second_address == $past(write_ptr));	
				assert($past(second_data) == fifo_data[second_address]);
			end
		end
	end
	

	reg [WIDTH - 1:0] first_data_read_out;
	reg [WIDTH - 1:0] second_data_read_out;
	
	initial first_data_is_read = 0;
	initial second_data_is_read = 0;

	always @(posedge read_clk)
	begin
		if(reset_rsync)
		begin  
			first_data_read_out <= 0;
			second_data_read_out <= 0;
			first_data_is_read <= 0;
			second_data_is_read <= 0;
		end

		`ifdef ENABLE_TWIN_WRITE_TEST	
		
			else if(read_en && !empty && first_data_is_written && !first_data_is_read && !second_data_is_read)
			begin
				first_data_read_out <= read_data;
				first_data_is_read <= 1;	
			end
			
			else if(read_en && !empty && second_data_is_written && !second_data_is_read)
			begin
				second_data_read_out <= read_data;
				second_data_is_read <= 1;	
			end
			
		`else
			else begin
				first_data_read_out <= read_data;
				second_data_read_out <= read_data;
				first_data_is_read <= 1;
				second_data_is_read <= 1;
			end
		`endif
	end

	always @($global_clock)
	begin
		if(first_clock_had_passed && ($rose(read_clk)))
		begin
			if($past(reset_rsync))
			begin
				assert(first_data_is_read == 0);
				assert(second_data_is_read == 0);
			end

			`ifdef ENABLE_TWIN_WRITE_TEST
			
				else if($past(read_en) && !$past(empty) && $past(first_data_is_written) && !$past(first_data_is_read) && !$past(second_data_is_read))
				begin
					assert(first_data_read_out == $past(read_data));				
					assert(first_data_is_read == 1);	
				end
				
				else if($past(read_en) && !$past(empty) && $past(second_data_is_written) && !$past(second_data_is_read))
				begin
					assert(second_data_read_out == $past(read_data));
					assert(second_data_is_read == 1);
				end
				
			`else
				else begin
					assert(first_data_read_out == $past(read_data));				
					assert(first_data_is_read == 1);	
					assert(second_data_read_out == $past(read_data));
					assert(second_data_is_read == 1);									
				end
			`endif
		end
	end

`endif

`ifdef FORMAL
	// mechanism needed for 'full' and 'empty' coverage check
	
	// writes to FIFO for many clock cycles, then
	// read from FIFO for many clock cycles
	
	// As for why this is needed at all, see https://math.stackexchange.com/a/4314823/625099 and
	// https://www.reddit.com/r/askmath/comments/r0hp2o/simple_gray_code_question/
	
	// for this particular test, we need NUM_ENTRIES to be power of 2 
	// since address rollover (MSB flipping) mechanism is used to check whether 
	// every FIFO entries had been visited at least twice
	localparam CYCLES_FOR_FULL_EMPTY_CHECK = NUM_ENTRIES; 
	
	reg [$clog2(CYCLES_FOR_FULL_EMPTY_CHECK):0] write_counter_loop_around_fifo;
	reg [$clog2(CYCLES_FOR_FULL_EMPTY_CHECK):0] read_counter_loop_around_fifo;	
	reg [$clog2(CYCLES_FOR_FULL_EMPTY_CHECK):0] previous_write_counter_loop_around_fifo;
	reg [$clog2(CYCLES_FOR_FULL_EMPTY_CHECK):0] previous_read_counter_loop_around_fifo;	
		
	initial write_counter_loop_around_fifo = 0;
	initial read_counter_loop_around_fifo = 0;
	initial previous_write_counter_loop_around_fifo = 0;
	initial previous_read_counter_loop_around_fifo = 0;
	
	always @(posedge write_clk)
	begin
		if(test_write_en)
			write_counter_loop_around_fifo <= write_counter_loop_around_fifo + 1;
			
		else write_counter_loop_around_fifo <= 0;
			
		previous_write_counter_loop_around_fifo <= write_counter_loop_around_fifo;
	end

	always @(posedge read_clk)
	begin
		if(test_read_en)
			read_counter_loop_around_fifo <= read_counter_loop_around_fifo + 1;
			
		else read_counter_loop_around_fifo <= 0;
		
		previous_read_counter_loop_around_fifo <= read_counter_loop_around_fifo;
	end

	
	// initially no testing
	reg test_write_en, previous_test_write_en;
	reg test_read_en;	
	initial test_write_en = 0;
	initial test_read_en = 0;
	initial previous_test_write_en = 0;	
	
	reg [$clog2(CYCLES_FOR_FULL_EMPTY_CHECK):0] test_write_data;
	
	wire finished_loop_writing =  // every FIFO entries had been visited at least twice
			(write_counter_loop_around_fifo == 0) && (&previous_write_counter_loop_around_fifo);
	
	always @(posedge write_clk)
	begin
		if(reset_wsync || finished_loop_writing)
		begin
			test_write_en <= 0;
			test_write_data <= 0;
		end
		
		else begin
			test_write_en <= second_data_is_read;  // starts after twin-write test
			test_write_data <= test_write_data + second_data_is_read;  // for easy tracking on write test progress
		end
	end

	reg had_finished_loop_writing;
	initial had_finished_loop_writing = 0;

	always @(posedge write_clk) 
	begin
		previous_test_write_en <= test_write_en;
		had_finished_loop_writing <= finished_loop_writing;
	end

	wire finished_loop_reading =  // every FIFO entries had been visited at least twice
			(read_counter_loop_around_fifo == 0) && (&previous_read_counter_loop_around_fifo);

	always @(posedge read_clk)
	begin
		if(reset_rsync || finished_loop_reading)
		begin
			test_read_en <= 0;
		end
		
		else begin
			test_read_en <= ((second_data_is_read) &&  // starts after twin-write test
							 (had_finished_loop_writing));  // finished write testing;	
		end
	end

	always @(posedge write_clk)
	begin
		if(test_write_en) 
		begin
			assume(write_en);
			assume(!read_en);  // write testing first, followed by read testing
			assume(write_data == test_write_data);
		end
	end

	always @(posedge read_clk)
	begin
		if(test_read_en) assume(read_en);
	end

	always @(*)
	begin
		if(test_write_en || test_read_en)
		begin
			assume(!write_reset);
			assume(!read_reset);
		end
	end
		
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
	always @(posedge write_clk)
		cover(first_write_clock_had_passed && write_reset);

	always @(posedge read_clk)
		cover(first_read_clock_had_passed && read_reset);


	always @($global_clock)
	if (first_clock_had_passed && reset_rsync_is_done)
		cover((empty)&&(!$past(empty)));

	always @(*)
	if (first_clock_had_passed && reset_wsync_is_done)
		cover(full);

	always @(posedge write_clk)
	if (first_write_clock_had_passed && reset_wsync_is_done)
		cover((write_en)&&(full));

	always @(posedge write_clk)
	if (first_write_clock_had_passed && reset_wsync_is_done)
		cover($past(full)&&(!full));

	always @(posedge write_clk)
		cover((full)&&(write_en));

	always @(posedge write_clk)
		cover(write_en);

	always @(posedge read_clk)
		cover((empty)&&(read_en));

	always @(posedge read_clk)
	if (first_read_clock_had_passed && reset_rsync_is_done)
		cover($past(!empty)&&($past(read_en))&&(empty));
		
	always @(posedge read_clk)
		cover(first_read_clock_had_passed && (finished_loop_reading));
		
`endif

endmodule
