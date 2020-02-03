
import edu.umn.crisys.plexil.java.plx.*;
import edu.umn.crisys.plexil.java.world.*;
import edu.umn.crisys.plexil.java.values.*;


public class MainScript {
	
	public static void main(String[] args) {
		JavaPlan.DEBUG = true;
		
		JavaPlan plan = new TargetPanorama();
		ExternalWorld world = new TargetPanoramaTimeoutScript();
		plan.setWorld(world);
		// Keep doing steps until the script runs out of events.
		while ( ! world.stop() ) {
			plan.doMacroStep();
			world.waitForNextEvent();
		}
	}
}
