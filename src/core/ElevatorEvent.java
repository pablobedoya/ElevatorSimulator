package core;

import event.EventType;

/**
 * Tipo de evento do elevador
 */
public class ElevatorEvent extends EventType {
    // Definição de eventos específicos, imitando enum
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
