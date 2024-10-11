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


// FORMULAS
// Insert the LTL formulas here
//ltl door1 { ... }


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
// Status of trash bin
bin_t bin_status;

// Maximal capacity of trash bin
byte max_capacity;

// User information
bool has_trash;


// CHANNELS
// Asynchronous channel to give command to doors and lock
chan change_bin = [1] of { mtype:comp, mtype:pos };
// Synchronous channel to acknowledge change in bin
chan bin_changed = [0] of { mtype:comp, bool };
// Synchronous channel to indicate that user closed the door
chan user_closed_outer_door = [0] of { bool };

// Synchronous channels to communicate with weight sensors in trap doors
chan weigh_trash = [0] of { bool };
chan trash_weighted = [0] of { byte };

// Synchronous channel to communicate with ram
chan change_ram = [0] of { mtype:ram_pos };
chan ram_changed = [0] of { bool };

// Asynchronous channel to communicate with the user
chan scan_card_user = [NO_USERS] of { byte };
chan can_deposit_trash = [NO_USERS] of { byte, bool };

// Synchronous channel to communicate with server
chan check_user = [0] of { byte };
chan user_valid = [0] of { byte, bool };

// Asynchronous channel to communicate with trash truck
chan request_truck = [NO_BINS] of { byte };
chan change_truck = [1] of { mtype:truck_pos, byte };
// Synchronous channel for communication between trash truck and trash bin
chan empty_bin = [0] of { bool };
chan bin_emptied = [0] of { bool };


// PROCESSES
// Trash bin process type.
// It models the physical components (doors, ram, sensors).
proctype bin(byte bin_id) {
	do
	// Outer door
	:: change_bin?OuterDoor, closed ->
		if
		:: bin_status.out_door == open ->
			bin_status.out_door = closed;
			bin_changed!OuterDoor, true;
			user_closed_outer_door!true;
		fi
	:: change_bin?OuterDoor, open ->
		if
		:: bin_status.out_door == closed && bin_status.lock_out_door == open ->
			bin_status.out_door = open;
			bin_changed!OuterDoor, true;
		fi
	:: change_bin?LockOuterDoor, closed ->
		if
		:: bin_status.lock_out_door == open && bin_status.out_door == closed ->
			atomic {
				bin_status.lock_out_door = closed;
				// Check if trash now falls trough
				if
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == closed && bin_status.trash_on_trap_door == 0 ->
					// Trash in outer door falls on trap door
					bin_status.trash_on_trap_door = bin_status.trash_in_outer_door;
					bin_status.trash_in_outer_door = 0;
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == closed && bin_status.trash_on_trap_door > 0 ->
					// Trash cannot fall through because there is already trash
					skip;
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == open ->
					// Trash in outer door falls through trap door
					bin_status.trash_uncompressed = bin_status.trash_uncompressed + bin_status.trash_in_outer_door;
					bin_status.trash_in_outer_door = 0;
				fi
			}
			bin_changed!LockOuterDoor, true;
		fi
	:: change_bin?LockOuterDoor, open ->
		if
		:: bin_status.lock_out_door == closed && bin_status.out_door == closed ->
			bin_status.lock_out_door = open;
			bin_changed!LockOuterDoor, true;
		fi
	// Trap door
	:: weigh_trash?true ->
		if
		:: bin_status.trap_door == closed ->
			trash_weighted!bin_status.trash_on_trap_door;
		fi
	:: change_bin?TrapDoor, closed ->
		if
		:: bin_status.trap_door == open && bin_status.ram == idle ->
			bin_status.trap_door = closed;
			bin_changed!TrapDoor, true;
		:: bin_status.trap_door == open && bin_status.ram == compress ->
			bin_status.trap_destroyed = true;
			bin_changed!TrapDoor, false;
		fi
	:: change_bin?TrapDoor, open ->
		if
		:: bin_status.trap_door == closed ->
			atomic {
				bin_status.trap_door = open;
				// Trash on trap door falls through
				if
				:: bin_status.trash_on_trap_door > 0 ->
					bin_status.trash_uncompressed = bin_status.trash_uncompressed + bin_status.trash_on_trap_door;
					bin_status.trash_on_trap_door = 0;
				:: else ->
					skip;
				fi
			}
			bin_changed!TrapDoor, true;
		fi
	// Vertical ram
	:: change_ram?compress ->
		if
		:: bin_status.ram == idle ->
			atomic {
				bin_status.ram = compress;
				if
				:: bin_status.trap_door == open ->
					// Compress trash
					bin_status.trash_compressed = bin_status.trash_compressed + bin_status.trash_uncompressed / 2;
					bin_status.trash_uncompressed = 0;
				:: bin_status.trap_door == closed ->
					// Trap doors are destroyed
					bin_status.trap_destroyed = true;
				fi
			}
			ram_changed!true;
		fi
	:: change_ram?idle ->
		if
		:: bin_status.ram == compress ->
			bin_status.ram = idle;
			ram_changed!true;
		fi
	// Emptying through trash truck
	:: empty_bin?true ->
		if
		:: bin_status.out_door == closed && bin_status.lock_out_door == closed && bin_status.ram == idle ->
			atomic {
				bin_status.trash_compressed = 0;
				bin_status.trash_uncompressed = 0;
			}
			bin_emptied!true;
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
		skip;
	od
}


// User process type.
// The user tries to deposit trash.
proctype user(byte user_id; byte trash_size) {
	do
	// Get another bag of trash
	:: !has_trash ->
		has_trash = true;
	// Try to deposit trash
	:: has_trash ->
		// Scan card
		scan_card_user!user_id;
		if
		:: can_deposit_trash?user_id, true ->
			bin_changed?LockOuterDoor, true;
			// Open door
			change_bin!OuterDoor, open;
			bin_changed?OuterDoor, true;
			atomic{
				if
				:: bin_status.trash_in_outer_door == 0 ->
					// Deposit trash
					bin_status.trash_in_outer_door = trash_size;
					has_trash = false;
				:: bin_status.trash_in_outer_door > 0 ->
					// Cannot deposit trash
					skip;
				fi
			}
			// Close door
			change_bin!OuterDoor, closed;
			bin_changed?OuterDoor, true;
		:: can_deposit_trash?user_id, false ->
			skip;
		fi
	od
}


// DUMMY main control process type.
// Remodel it to control the trash bin system and handle requests by users!
proctype main_control() {
	byte user_id;
	do
	:: scan_card_user?user_id ->
		skip;
	od
}

// Initial process that instantiates all other processes and
// creates the initial trash bin situation.
init {
	byte proc;
	atomic {
		// In the code below, the individual trash bins are initialised.
		// The assumption here is that N == 1.
		// When generalising the model for multiple bin, make sure that the do-statement is altered!
		proc = 0;
		do
		:: proc < NO_BINS ->
			// Status of trash bin
			bin_status.out_door = closed;
			bin_status.lock_out_door = closed;
			bin_status.trap_door = closed;
			bin_status.ram = idle;
			bin_status.trash_in_outer_door = 0;
			bin_status.trash_on_trap_door = 0;
			bin_status.trash_compressed = 0;
			bin_status.trash_uncompressed = 0;
			bin_status.full_capacity = false;
			bin_status.trap_destroyed = false;
			max_capacity = 2;
			run bin(proc);
			proc++;
		:: proc == NO_BINS ->
			break;
		od;

		// Start the user process
		proc = 0;
		byte trash_size = 2;
		has_trash = true;
		run user(proc, trash_size);

		// Start the server process
		run server();
		// Start the trash truck process
		run truck();

		// Start the control process for the trash bin
		run main_control();
	}
}
