package core;

/**
 * 电梯状态对象
 */
public class ElevatorStatus {
    int currentFloor = 1; // 当前楼层
    Direction direction = Direction.UP; // 当前的移动方向
    int targetFloor = 0; // 要移动到的目标楼层
    boolean isOpen = false; // 电梯门是否打开
    boolean isMoving = true; // 电梯是否在移动,默认为true,这样一开始就能开门
}
