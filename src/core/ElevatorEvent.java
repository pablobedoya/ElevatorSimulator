package core;

import event.EventType;

/**
 * 电梯事件类型
 */
public class ElevatorEvent extends EventType {
    // 定义具体事件,模仿枚举
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
