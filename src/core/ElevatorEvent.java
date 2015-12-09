package core;

import event.EventType;

/**
 * Tipo de evento do elevador
 */
public class ElevatorEvent extends EventType {
    // Defini��o de eventos espec�ficos, imitando enum
    public static ElevatorEvent
            LAUNCH = stub(),
            STOP = stub(),
            OUTER_PRESSED = stub(),
            INNER_PRESSED = stub(),
            MOVING = stub(),
            PENDING = stub(),
            OPEN = stub(),
            CLOSE = stub(),
            ENTER = stub(),
            LEAVE = stub();

    public static ElevatorEvent stub(){
        return new ElevatorEvent();
    }
}
