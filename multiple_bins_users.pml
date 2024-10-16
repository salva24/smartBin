/*
	Trash bin system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one trash bin and one user.

	This file contains the environment for the single trash bin system part of the assignment.
	It contains:
	- a specification of the trash bin
	- a specification of a simple server
	- a specification of a user
	- a specification of a trash truck
	- a (dummy) specification of the main controller
	- formulas to check the requested properties
*/


// CONSTANTS
// The number of trash bins.
#define NO_BINS 1
// The number of users.
#define NO_USERS 1
#define USER_ID 0
#define BIN_ID 0




// FORMULAS
// Insert the LTL formulas here
// ram1 The vertical ram is only used when the outer door is closed and locked. (Safety)
// G ((ram = compress) -> (out_door = closed && lock_out_door = closed))
//for all bin_id
ltl ram1 { [](bin_status[bin_id].ram == compress -> (bin_status[bin_id].out_door == closed && bin_status[bin_id].lock_out_door == closed)) }

// The vertical ram is not used when the interior of the trash bin is empty. (Safety)
// G ((ram = compress) -> (trash_uncompressed > 0 || trash_compressed > 0))
//for all bin_id
ltl ram2 { [](bin_status[bin_id].ram == compress -> (bin_status[bin_id].trash_uncompressed > 0 || bin_status[bin_id].trash_compressed > 0)) }

// The outer door can only be opened if no trash is in it. (Safety)
// G ((out_door = open) -> (trash_in_outer_door = 0))
//for all bin_id
ltl door1 { [](bin_status[bin_id].out_door == open -> bin_status[bin_id].trash_in_outer_door == 0) }

// The outer door can only be locked if the trap door is closed and no trash is on the trap door. (Safety)
// G ((lock_out_door = closed) -> (trap_door = closed && trash_on_trap_door = 0))
//for all bin_id
ltl door2 { [](bin_status[bin_id].lock_out_door == closed -> (bin_status[bin_id].trap_door == closed && bin_status[bin_id].trash_on_trap_door == 0)) }

// Every time the trash bin is full, it is eventually not full anymore. (Liveness)
// G (full_capacity -> F (!full_capacity))
//for all bin_id
ltl capacity1 { [](bin_status[bin_id].full_capacity -> <>(!bin_status[bin_id].full_capacity)) }

// The user always eventually has no trash. (Liveness)
// G (has_trash -> F (!has_trash))
//for all user_id
ltl user1 { [](<>(!has_trash[user_id])) }

// Every time the user has trash they can deposit their trash. (Liveness)
// G (has_trash -> F (can_deposit_trash))
//for all user_id
ltl user2 { [](has_trash[user_id] -> <>(!has_trash[user_id])) }//it does not matter which is the value of bin_id
// ltl user2 { []((?bin_id && has_trash[user_id]) -> <>can_deposit_trash?user_id, bin_id, true) }//it does not matter which is the value of bin_id

// Every time the truck is requested for a trash bin, the truck has eventually emptied the bin (Liveness)
// G (request_truck -> F (bin_emptied))
//for all bin_id
ltl truck1 { [](request_truck?[BIN_ID] -> <>bin_emptied[BIN_ID]) }



// DATATYPES
// Type for components
mtype:comp = { OuterDoor, LockOuterDoor, TrapDoor }
// Type for door position.
mtype:pos = { closed, open };
// Type for ram position.
mtype:ram_pos = { idle, compress };
// Type for truck position.
mtype:truck_pos = { arrived, start_emptying, emptied };

// Datatype to store information on the trash bin 
typedef bin_t {
	// Status of doors and ram
	mtype:pos out_door;
	mtype:pos lock_out_door;
	mtype:pos trap_door;
	mtype:ram_pos ram;
	// Location of trash
	byte trash_in_outer_door;
	byte trash_on_trap_door;
	// Current level of trash
	byte trash_compressed;
	byte trash_uncompressed;
	// Exceptional behavior
	bool full_capacity;
	bool trap_destroyed;
}


// VARIABLES
// Array of status of trash bin
bin_t bin_status[NO_BINS];

// Maximal capacity of each trash bin (I assume they can be different)
byte max_capacity[NO_BINS];

// Array of users information
bool has_trash[NO_USERS];


// CHANNELS
// Asynchronous channel to give command to doors and lock
chan change_bin[NO_BINS] = [1] of {byte, mtype:comp, mtype:pos };//for each bin
// Synchronous channel to acknowledge change in bin
chan bin_changed[NO_BINS] = [0] of {byte, mtype:comp, bool };
// Synchronous channel to indicate that user closed the door
chan user_closed_outer_door[NO_BINS] = [0] of { bool };

// Synchronous channels to communicate with weight sensors in trap doors
chan weigh_trash[NO_BINS] = [0] of { bool };
chan trash_weighted[NO_BINS] = [0] of { byte };

// Synchronous channel to communicate with ram
chan change_ram[NO_BINS] = [0] of { mtype:ram_pos };
chan ram_changed[NO_BINS] = [0] of { bool };

// Asynchronous channel to communicate with the user
chan scan_card_user = [NO_USERS] of { byte };
chan can_deposit_trash = [NO_USERS] of { byte,byte, bool };//user_id, bin_id, bool

// Synchronous channel to communicate with server
chan check_user = [0] of { byte };
chan user_valid = [0] of { byte, bool };

// Asynchronous channel to communicate with trash truck
chan request_truck = [NO_BINS] of { byte };
chan change_truck = [1] of { mtype:truck_pos, byte };
// Synchronous channel for communication between trash truck and trash bin
chan empty_bin[NO_BINS] = [0] of { bool };
chan bin_emptied[NO_BINS] = [0] of { bool };


// PROCESSES
// Trash bin process type.
// It models the physical components (doors, ram, sensors).
proctype bin(byte bin_id) {
	do
	// Outer door
	:: change_bin[bin_id]?OuterDoor, closed ->
		if
		:: bin_status[bin_id].out_door == open ->
			bin_status[bin_id].out_door = closed;
			bin_changed[bin_id]!OuterDoor, true;
			user_closed_outer_door[bin_id]!true;
		fi
	:: change_bin[bin_id]?OuterDoor, open ->
		if
		:: bin_status[bin_id].out_door == closed && bin_status[bin_id].lock_out_door == open ->
			bin_status[bin_id].out_door = open;
			bin_changed[bin_id]!OuterDoor, true;
		fi
	:: change_bin[bin_id]?LockOuterDoor, closed ->
		if
		:: bin_status[bin_id].lock_out_door == open && bin_status[bin_id].out_door == closed ->
			atomic {
				bin_status[bin_id].lock_out_door = closed;
				// Check if trash now falls trough
				if
				:: bin_status[bin_id].trash_in_outer_door > 0 && bin_status[bin_id].trap_door == closed && bin_status[bin_id].trash_on_trap_door == 0 ->
					// Trash in outer door falls on trap door
					bin_status[bin_id].trash_on_trap_door = bin_status[bin_id].trash_in_outer_door;
					bin_status[bin_id].trash_in_outer_door = 0;
				:: bin_status[bin_id].trash_in_outer_door > 0 && bin_status[bin_id].trap_door == closed && bin_status[bin_id].trash_on_trap_door > 0 ->
					// Trash cannot fall through because there is already trash
					skip;
				:: bin_status[bin_id].trash_in_outer_door > 0 && bin_status[bin_id].trap_door == open ->
					// Trash in outer door falls through trap door
					bin_status[bin_id].trash_uncompressed = bin_status[bin_id].trash_uncompressed + bin_status[bin_id].trash_in_outer_door;
					bin_status[bin_id].trash_in_outer_door = 0;
				fi
			}
			bin_changed[bin_id]!LockOuterDoor, true;
		fi
	:: change_bin[bin_id]?LockOuterDoor, open ->
		if
		:: bin_status[bin_id].lock_out_door == closed && bin_status[bin_id].out_door == closed ->
			bin_status[bin_id].lock_out_door = open;
			bin_changed[bin_id]!LockOuterDoor, true;
		fi
	// Trap door
	:: weigh_trash[bin_id]?true ->
		if
		:: bin_status[bin_id].trap_door == closed ->
			trash_weighted[bin_id]!bin_status[bin_id].trash_on_trap_door;
		fi
	:: change_bin[bin_id]?TrapDoor, closed ->
		if
		:: bin_status[bin_id].trap_door == open && bin_status[bin_id].ram == idle ->
			bin_status[bin_id].trap_door = closed;
			bin_changed[bin_id]!TrapDoor, true;
		:: bin_status[bin_id].trap_door == open && bin_status[bin_id].ram == compress ->
			bin_status[bin_id].trap_destroyed = true;
			bin_changed[bin_id]!TrapDoor, false;
		fi
	:: change_bin[bin_id]?TrapDoor, open ->
		if
		:: bin_status[bin_id].trap_door == closed ->
			atomic {
				bin_status[bin_id].trap_door = open;
				// Trash on trap door falls through
				if
				:: bin_status[bin_id].trash_on_trap_door > 0 ->
					bin_status[bin_id].trash_uncompressed = bin_status[bin_id].trash_uncompressed + bin_status[bin_id].trash_on_trap_door;
					bin_status[bin_id].trash_on_trap_door = 0;
				:: else ->
					skip;
				fi
			}
			bin_changed[bin_id]!TrapDoor, true;
		fi
	// Vertical ram
	:: change_ram[bin_id]?compress ->
		if
		:: bin_status[bin_id].ram == idle ->
			atomic {
				bin_status[bin_id].ram = compress;
				if
				:: bin_status[bin_id].trap_door == open ->
					// Compress trash
					bin_status[bin_id].trash_compressed = bin_status[bin_id].trash_compressed + bin_status[bin_id].trash_uncompressed / 2;
					bin_status[bin_id].trash_uncompressed = 0;
				:: bin_status[bin_id].trap_door == closed ->
					// Trap doors are destroyed
					bin_status[bin_id].trap_destroyed = true;
				fi
			}
			ram_changed[bin_id]!true;
		fi
	:: change_ram[bin_id]?idle ->
		if
		:: bin_status[bin_id].ram == compress ->
			bin_status[bin_id].ram = idle;
			ram_changed[bin_id]!true;
		fi
	// Emptying through trash truck
	:: empty_bin[bin_id]?true ->
		if
		:: bin_status[bin_id].out_door == closed && bin_status[bin_id].lock_out_door == closed && bin_status[bin_id].ram == idle ->
			atomic {
				bin_status[bin_id].trash_compressed = 0;
				bin_status[bin_id].trash_uncompressed = 0;
			}
			bin_emptied[bin_id]!true;
		fi
	od
}

// Server process type.
// It models the central backend and administration interface.
proctype server() {
	byte user_id;
	do
	// Check validity of card
	:: check_user?user_id ->
		if
		// Do not accept cards from user with id 42
		:: user_id != 42 ->
			user_valid!user_id, true;
		:: user_id == 42 ->
			user_valid!user_id, false;
		fi
	od
}

// Trash truck process type.
// Remodel it to control the trash truck and handle requests by the controller!
proctype truck() {
	byte bin_id;
	do
	:: request_truck?bin_id ->
		change_truck!arrived, bin_id;
		change_truck? start_emptying, bin_id;
		empty_bin[bin_id]!true;
		bin_emptied[bin_id]?true;
		change_truck!emptied, bin_id;
	od
}


// User process type.
// The user tries to deposit trash.
proctype user(byte user_id; byte trash_size) {
	byte bin_id;
	do
	// Get another bag of trash
	:: !has_trash[user_id] ->
		has_trash[user_id] = true;
	// Try to deposit trash
	:: has_trash[user_id] ->
		// Scan card
		scan_card_user!user_id;
		if
		:: can_deposit_trash?user_id, bin_id, true ->
			bin_changed[bin_id]?LockOuterDoor, true;
			// Open door
			change_bin[bin_id]!OuterDoor, open;
			bin_changed[bin_id]?OuterDoor, true;
			atomic{
				if
				:: bin_status[bin_id].trash_in_outer_door == 0 ->
					// Deposit trash
					bin_status[bin_id].trash_in_outer_door = trash_size;
					has_trash[user_id] = false;
				:: bin_status[bin_id].trash_in_outer_door > 0 ->
					// Cannot deposit trash
					skip;
				fi
			}
			// Close door
			change_bin[bin_id]!OuterDoor, closed;
			bin_changed[bin_id]?OuterDoor, true;
		:: can_deposit_trash?user_id,bin_id, false ->
			skip;
		fi
	od
}


// DUMMY main control process type.
// Remodel it to control the trash bin system and handle requests by users!
proctype main_control() {
    byte user_id;
    bool valid;
    byte trash_weight;
    byte bin_id;
    
    do
    :: bin_id = 0;//first we are gonna empty all the bins
       do
       :: bin_id < NO_BINS ->    // Iterate over all bins
           if
           :: bin_status[bin_id].full_capacity -> // We need to empty the bin
               request_truck!bin_id;
           :: else -> skip;  // Continue if not full
           fi;
           bin_id++;          // Move to the next bin
       :: bin_id == NO_BINS -> break; // When all bins have been processed
       od;
    
    	scan_card_user?user_id; 
        check_user!user_id;                
        user_valid?user_id, valid ->        // Wait for server response
            if
            :: valid -> 
                // We look for a bin which is not full
                bin_id = 0;
                do
                :: bin_id < NO_BINS -> 
                    if
                    :: !bin_status[bin_id].full_capacity ->  
                        can_deposit_trash!user_id,bin_id, true;
                        
                        // Wait for the outer door to be closed
                        user_closed_outer_door[bin_id]?true; 
                        
                        // Close and lock the outer door
                        change_bin[bin_id]!LockOuterDoor, closed; 
                        
                        // Weigh the trash
                        weigh_trash[bin_id]!true;  
                        trash_weighted[bin_id]?trash_weight;
                        
                        // Open the trap door (we assume the trap door is closed)
                        assert(bin_status[bin_id].trap_door == closed);
                        change_bin[bin_id]!TrapDoor, open;
                        bin_changed[bin_id]?TrapDoor, true;
                        
                        // Compress the trash
                        change_ram[bin_id]!compress;
                        ram_changed[bin_id]?true;
                        change_ram[bin_id]!idle;
                        ram_changed[bin_id]?true;
                        
                        // Close trap door
                        assert(bin_status[bin_id].trap_door == open);
                        change_bin[bin_id]!TrapDoor, closed;
                        bin_changed[bin_id]?TrapDoor, true;
                        
                        // Checking if bin is full
                        if
                        :: (bin_status[bin_id].trash_uncompressed + bin_status[bin_id].trash_compressed) >= max_capacity[bin_id] -> 
                            bin_status[bin_id].full_capacity = true;
                        :: else -> skip;
                        fi;
                        
                        break; // Stop the loop beacause bin has been processed
                    :: else -> skip;  // If full, try the next bin
                    fi;
                    bin_id++; 
                :: bin_id == NO_BINS -> // All bins have been checked and are full
					can_deposit_trash!user_id,NO_BINS, false;  // No available bins: there is no bin id
                    break;  
                od;
                
            :: else -> can_deposit_trash!user_id,NO_BINS, false; // Invalid user there is no bin id
            fi;
            
    od;
}



// Initial process that instantiates all other processes and
// creates the initial trash bin situation.
init {
	byte proc;
	atomic {

		proc = 0;
		do
		:: proc < NO_BINS ->
			// Status of trash bin
			bin_status[proc].out_door = closed;
			bin_status[proc].lock_out_door = closed;
			bin_status[proc].trap_door = closed;
			bin_status[proc].ram = idle;
			bin_status[proc].trash_in_outer_door = 0;
			bin_status[proc].trash_on_trap_door = 0;
			bin_status[proc].trash_compressed = 0;
			bin_status[proc].trash_uncompressed = 0;
			bin_status[proc].full_capacity = false;
			bin_status[proc].trap_destroyed = false;
			max_capacity[proc] = 2;
			run bin(proc);
			proc++;
		:: proc == NO_BINS ->
			break;
		od;

		// Start the users processes
		proc = 0;
		byte trash_size = 2;//I assume all users ahs the same ammount of trash (could be easily changed)
		do
		:: proc < NO_USERS ->
			// Status of User
			has_trash[proc] = true;
			run user(proc, trash_size);
			proc++;
		:: proc == NO_USERS ->
			break;
		od;

		// Start the server process
		run server();
		// Start the trash truck process
		run truck();

		// Start the control process for the trash bin
		run main_control();
	}
}
