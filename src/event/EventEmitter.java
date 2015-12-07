package event;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * 事件发生器基类
 * 所有想要获得事件监听/发送能力的类需要继承这个基类
 */
public class EventEmitter {
    /**
     * 添加事件监听
     * @param type 事件类型
     * @param callback 回调函数
     */
    public void on(EventType type, Callback callback)  {
        List<Callback> callbacks = getCallbacks(type);
        callbacks.add(callback);
    }

    /**
     * 发送指定的事件
     * @param type 事件类型
     * @param data 事件数据,可选
     * @param <T> 范型类型
     */
    public <T> void emit(EventType type, T... data){
        List<Callback> callbacks = getCallbacks(type);
        callbacks.stream().forEach( callback -> callback.run(data.length>0?data[0]:null));
    }

    private Map<EventType,List<Callback>> callbackMap = new HashMap<EventType,List<Callback>>();

    /**
     * 获取指定事件类型对应的回调函数列表
     * 如果还没有列表,就立即创建一个(惰性初始化)
     * @param type 事件类型
     * @return 事件类型对应回调函数列表(必不为空)
     */
    private List<Callback> getCallbacks(EventType type){
        List<Callback> callbacks = callbackMap.get(type);
        if(callbacks == null){
            callbacks = new LinkedList<Callback>();
            callbackMap.put(type, callbacks);
        }

        return callbacks;
    }
}
