/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Jensen 
 *     Christian Frost
 *     Kasperkow.
 * 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Public License v3.0
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/gpl.html
 * 
 * Contributors:
 *     Andreas Engelbredt Dalsgaard <andreas.dalsgaard@gmail.com> - Changes to run on  jop SCJ implementation
 *     Casper Jensen <semadk@gmail.com> - Initial implementation
 *     Christian Frost <thecfrost@gmail.com> - Initial implementation
 *     ckow <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump.actuators;

import gov.nasa.jpf.symbc.realtime.minepump.legosim.lib.Motor;

public class GenericActuator {
    private static final int SPEED = 70;

    protected Motor legomotor;

    public GenericActuator(int id) {
        
    }
    
    public void start() {
      
    }
}
/*this.legomotor.setMotorPercentage(Motor.STATE_FORWARD, false, SPEED);*/
