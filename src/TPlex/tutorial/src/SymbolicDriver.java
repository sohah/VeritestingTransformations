
import edu.umn.crisys.plexil.java.plx.*;
import edu.umn.crisys.plexil.java.world.*;
import edu.umn.crisys.plexil.java.values.*;


public class SymbolicDriver {
	public static void main(String[] args) {
		JavaPlan plan = new TargetPanorama();
		ExternalWorld world = configureSymbolicExternalWorld();
		plan.setWorld(world);
		// Keep doing steps until the root node has an outcome.
		// We could also perform some specific number of steps, or
		// run indefinitely.
		while ( plan.getRootNodeOutcome().isUnknown() ) {
			plan.doMacroStep();
			world.waitForNextEvent();
		}
	}
	private static ExternalWorld configureSymbolicExternalWorld(){
		// Create our SymbolicExternalWorld and then configure it.
		SymbolicExternalWorld world = new SymbolicExternalWorld();
		// Respond to all the commands with either success or failure
		world.addCommand("rover_drive", CommandHandleState.COMMAND_SUCCESS,
				CommandHandleState.COMMAND_FAILED);
		world.addCommand("rover_stop", CommandHandleState.COMMAND_SUCCESS,
				CommandHandleState.COMMAND_FAILED);
		world.addCommand("take_navcam", CommandHandleState.COMMAND_SUCCESS,
				CommandHandleState.COMMAND_FAILED);
		world.addCommand("take_pancam", CommandHandleState.COMMAND_SUCCESS,
				CommandHandleState.COMMAND_FAILED);
		// The Lookup(target_in_view) should return a boolean.
		world.addLookup("target_in_view", PlexilType.BOOLEAN);
		// Time should be an integer.
		world.addIncreasingLookup("time", PlexilType.INTEGER);
		return world;
	}
}
