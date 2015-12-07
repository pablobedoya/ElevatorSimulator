package core;

import util.Log;

/**
 * 电梯主线程行为
 */
public class ElevatorThread implements Runnable{
    public static int TIME_INTERVAL = 1000;

    private Elevator ele;
    private ElevatorStatus status;
    public ElevatorThread(Elevator elevator){
        this.ele = elevator;
        this.status = elevator.status;
    }

    @Override
    public void run() {
        while(true){
            // 到达目标楼层,开门
            if(status.isMoving && status.currentFloor == status.targetFloor){
                status.isOpen = true;
                status.isMoving = false;
                ele.emit(ElevatorEvent.OPEN, status.currentFloor);
            }
            // 关门
            else if(status.isOpen){
                status.isOpen = false;
                ele.emit(ElevatorEvent.CLOSE, status.currentFloor);
            }
            // 没有达到目标楼层,则进行移动
            else if(status.targetFloor != 0 && status.currentFloor != status.targetFloor){
                if(status.currentFloor < status.targetFloor) moveFloor(status, true);
                else moveFloor(status, false);

                status.isMoving = true;

                ele.emit(ElevatorEvent.MOVING, status.currentFloor);
            }
            // 原地等待
            else{
                ele.emit(ElevatorEvent.PENDING);
            }

            try {
                Thread.sleep(TIME_INTERVAL);
            } catch (InterruptedException e) {
                Log.error("电梯主线程被中断", e);
                break;
            }
        }
    }

    /**
     * 将电梯的楼层移动一层
     * @param status 电梯状态对象
     * @param isIncrease 移动方向
     */
    private void moveFloor(ElevatorStatus status, boolean isIncrease){
        if(isIncrease){
            status.currentFloor++;
            if(status.currentFloor == 0)
                status.currentFloor++;
        }else{
            status.currentFloor--;
            if(status.currentFloor == 0)
                status.currentFloor--;
        }
    }
}
