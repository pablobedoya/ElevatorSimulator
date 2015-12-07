package core;

import event.Callback;
import event.EventEmitter;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * 电梯类
 */
public class Elevator extends EventEmitter{
    // 电梯请求列表
    private List<Request> requests = new LinkedList<>();
    // 电梯状态值
    ElevatorStatus status = new ElevatorStatus();

    /**
     * 电梯启动
     */
    public void launch() {
        // 启动电梯主线程
        new Thread(new ElevatorThread(this)).start();
        this.emit(ElevatorEvent.LAUNCH, status.currentFloor);

        // 移除所有已经到达的请求
        this.on(ElevatorEvent.OPEN, data -> {
            int currentFloor = (Integer) data;
            requests = requests.stream().filter((req) -> !(req.stopFloor == currentFloor))
                    .collect(Collectors.toList());
        });

        // 关门事件,执行下一个请求
        this.on(ElevatorEvent.CLOSE, data -> updateTarget());
    }

    /**
     * 电梯外部按钮被按下执行方法
     * @param direction 按下的方向
     * @param currentFloor 当前所在的楼层
     * @param presser 按下按钮的人
     * @return 自身,实现链式调用
     */
    public Elevator outerPress(Direction direction, int currentFloor, Human presser) {
        // 构造外部按钮请求,添加到外部请求队列中
        OuterRequest req = new OuterRequest()
                .setDirection(direction)
                .setCurrentFloor(currentFloor)
                .setPresser(presser);
        requests.add(req);

        // 触发事件
        this.emit(ElevatorEvent.OUTER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * 内部电梯按钮被按下执行方法
     * @param targetFloor 要去的楼层
     * @param presser 按下按钮的人
     * @return 电梯实例
     */
    public Elevator innerPress(int targetFloor, Human presser) {
        // 构造外部按钮请求,添加到外部请求队列中
        InnerRequest req = new InnerRequest()
                .setCurrentFloor(status.currentFloor)
                .setTargetFloor(targetFloor)
                .setPresser(presser);
        requests.add(req);

        // 触发事件
        this.emit(ElevatorEvent.INNER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * 更新电梯的移动目标
     * 间接触发电梯移动
     */
    private void updateTarget(){
        // 首先要处理的请求,之后给出具体的值
        Request first;
        // 将请求列表排序,如果电梯正在向上,则根据楼层高度倒序排列,优先处理最高楼层
        // 反之亦然
        sort(requests);
        if(requests.size() == 0) return;

        first = requests.get(0);
        // 设定目标楼层
        status.targetFloor = first.getStopFloor();
    }

    /**
     * 将所有请求按照优先级排序
     * @param requests 请求的集合
     */
    private void sort(List<Request> requests){
        // 电梯当前的楼层
        int currentFloor = status.currentFloor;
        Direction currentDirection = status.direction;

        // 以电梯向上为例,所有请求分成以下几类:
        // 1. 也是向上且请求楼层比当前当前电梯楼层高的
        // 2. 向下的请求
        // 3. 向上的请求且请求楼层比当前当前电梯楼层低的
        // 电梯向下时相反

        // 第一类请求
        List<Request> list1 = requests.stream().filter( req -> {
            // 是否同向
            boolean isSame = req.getDirection() == currentDirection;
            // 是否优先
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && isSuper;
        }).sorted( (lhs,rhs) -> {
            // 第一类中,电梯向上时,越低越优先
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        // 第二类请求
        List<Request> list2 = requests.stream().filter( req -> {
            // 取反向的
            boolean isSame = (req.getDirection() == currentDirection);
            return !isSame;
        }).sorted( (lhs,rhs) -> {
            // 第二类中,电梯向上时越高越优先
            if(currentDirection == Direction.UP){
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }else{
                return lhs.getStopFloor() - rhs.getStopFloor();
            }
        }).collect(Collectors.toList());


        // 第三类请求
        List<Request> list3 = requests.stream().filter( req -> {
            // 是否同向
            boolean isSame = req.getDirection() == currentDirection;
            // 是否优先
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && !isSuper;
        }).sorted( (lhs,rhs) -> {
            // 第三类中,电梯向上时越低越优先
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        requests.clear();

        // 组合三类请求
        requests.addAll(list1);
        requests.addAll(list2);
        requests.addAll(list3);
    }

    // 覆盖父类方法
    public <T> void emit(ElevatorEvent type, T... data) {
        super.emit(type, data);
    }
    // 覆盖父类方法
    public void on(ElevatorEvent type, Callback callback) {
        super.on(type, callback);
    }
}
