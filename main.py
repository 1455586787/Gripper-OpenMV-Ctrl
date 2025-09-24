import time, pyb,sensor
import mjpeg
from pyb import UART
import os
import image
import math
import lcd
sensor.reset()
sensor.set_pixformat(sensor.RGB565)
sensor.set_framesize(sensor.QVGA)  #320x240
sensor.skip_frames(time=2000)
sensor.set_auto_gain(True)   #自动增益  自动调整图像亮度 True
sensor.set_auto_whitebal(False) #白平衡 自动校正颜色，使白色物体在不同光照下显示正常 False
# sensor.set_hmirror(True)   #启用水平镜像
# sensor.set_vflip(True)   #启用垂直镜像
clock = time.clock()

#-------------全局变量---------------
# red_thresholds = [(22,41,4,48,7,41)]  # 红色阈值
# blue_thresholds = [(19,35,-8,19,-31,-10)]     # 蓝色阈值
# ROI = (30,30,260,180)
flag = 1 #开机机械臂初始标志
#红色
red_threshold = (45, 97, 54, 90, -14, 75)
red_threshold_stepplatfrom = (45, 97, 54, 90, -14, 75)
red_threshold_post = (45, 97, 54, 90, -14, 75)
red_threshold_warehouse = (45, 97, 54, 90, -14, 75)
#蓝色
blue_threshold = (30, 82, -37, 39, -66, -36) #(23, 73, -8, 45, -87, -47)  # (39, 85, -64, 60, -87, -13) # (38, 71, -7, 45, -87, -47) #
blue_threshold_stepplatfrom = (26, 69, -20, 43, -83, -22)  #(26, 69, -20, 43, -83, -22)  (18, 78, -38, 51, -82, -22)
blue_threshold_post = (18, 78, -38, 51, -82, -27)
blue_threshold_warehouse =  (10, 70, -18, 56, -90, -22)   # (35, 59, -85, 75, -105, -58)   (18, 78, -38, 51, -82, -27)  (23, 64, -24, 51, -94, -14)  (23, 64, -24, 51, -94, -14)
# 白色
white_threshold = (75, 96, -14, 26, -21, 19) #(65, 96, -32, 71, -13, 47)
# #颜色码
# red_color_code = 1
# blue_color_code = 2
# green_color_code = 4
# white_color_code = 8
# yellow_color_code = 16

ROI = (0,0,320,240)

stepplatfrom_roi = (70,0,320,170)
DISKROI = (0,0,320,150)
WHITEROI = (70,0,200,90)
color_data = []
color_blob_1 = None
#从STM32 接收到的数据，不会被清空
data_rx_stm32 = None

arm_step = 0
platfrom_step = 0
post_step = 0
warehouse_step = 0
inbound_step = 0

stepped_flag = 0  #区别左中右
#比例
ratio = None
platfrom_k1 = 0.057 #右
platfrom_k2 = 0.05 #中
platfrom_k3 = 0.05 #左
#解算后机械臂的位置
ball_y = None
ball_x = None

post_x_0 = None
post_y_0 = None

post_x_1 = None
post_y_1 = None
#主函数任务 状态机
task_flag = 0

color_state = 0
is_send_data = 1

group_index = 0
RFID_Buff = []  #接收stm32读取的RFID
RFID_Buff_index = 0
ID_14_index = None
empty_idx = None
#-----------------摄像头扫码-----------
qr_result = []
last_qr_result = None
#-------------扫码模块--------------------
qr_rx_buff = [0,0,0]  #二维码接收缓存
qr_rx_buff_last = None
#------------RFID和仓库坐标---------------
inbound_index = 0 #仓库位置索引
idx = 0 #对应篮筐位置索引
keys = [0x31,0x32,0x33,0x21,0x22,0x23,0x11,0x12,0x13,0x14]

#篮筐坐标
hoop_coordinates = [
    [13,20,38]   , [13,21,32.2] ,  #0
    [7, 20, 38]  , [7, 21.5, 32.6],
    [-6, 20, 38] , [-6, 21.5, 32.6],
    [-12,20,40] , [-12,21.5,32.6],
    # Second row
    [-13,14.5,38.5]    ,  [-13,14.5,33],
    [-5.5,14.5,38.5]  ,  [-5.5,14.5,33],
    [0,13,38]     ,  [0,13.6,34] ,
    [6,13,38.5]    ,  [6,14,33] ,
    [13,14,38.5]   ,  [13,14,33] ,
    #Third row
    [13,7.5,38.5]     ,  [13,7.5,33.6] ,
    [-13.5,7.5,38]  ,  [-13.5,7.5,33.6], #10 共11个
]
#仓库位置坐标
rfid_to_location = {
    #最上面第三行
    0x31 : ([7,14,55] , [15,29,52.5]),
    0x32 : ([0,12,55] , [0,29,52.5]),
    0x33 : ([-7,14,55] , [-15,29,52.5]),
    #中间一行
    0x21 : ([7,14,40] , [15,29,41]),
    0x22 : ([0,14,42] , [0,29,40]),
    0x23 : ([-7,14,42] , [-15,29,40]),
    #第一行
    0x11 :([7,14,32] , [14,29,30]), #([7,12,32.5] , [14,24,32.5]),
    0x12 : ([0,14,32] , [0,29,30]),  #([0,12,32.5] , [0,24,32.5]),
    0x13 : ([-7,14,32] , [-14,29,30]),  #([-7,12,32.5] , [-13,24,32.5]),
    #后面修改可以这样 ：3
    # rfid_to_location[0x11] = ([7,12,32.5], [14,24,32.5])
}
#利用二维码补充立体仓库货架位置  现在位置都有了，可以写搬运动作了
def qr_to_loocation():
    global qr_rx_buff,rfid_to_location
    if qr_rx_buff[0] == 0x33:
        rfid_to_location[0x13] = ([-7,14,32] , [-14,29,30])
    elif qr_rx_buff[0] == 0x32:
        rfid_to_location[0x12] = ([-7,14,32] , [-14,29,30])
    elif qr_rx_buff[0] == 0x31:
        rfid_to_location[0x11] = ([-7,14,32] , [-14,29,30])

    if qr_rx_buff[1] == 0x33:
        rfid_to_location[0x13] = ([0,14,32] , [0,29,30])
    elif qr_rx_buff[1] == 0x32:
        rfid_to_location[0x12] = ([0,14,32] , [0,29,30])
    elif qr_rx_buff[1] == 0x31:
        rfid_to_location[0x11] = ([0,14,32] , [0,29,30])

    if qr_rx_buff[2] == 0x33:
        rfid_to_location[0x13] = ([7,14,32] , [14,29,30])
    elif qr_rx_buff[2] == 0x32:
        rfid_to_location[0x12] = ([7,14,32] , [14,29,30])
    elif qr_rx_buff[2] == 0x31:
        rfid_to_location[0x11] = ([7,14,32] , [14,29,30])
    print("3 层 1 列",rfid_to_location[0x11])
    print("3 层 2 列",rfid_to_location[0x12])
    print("3 层 3 列",rfid_to_location[0x13])
'''
0x11 0x12 0x13  --> 0x31 0x32 0x33
rfid_to_location = {
    0x31 : []
    0x32 : []
    0x33 : []
}
keys = list(rfid_to_location.keys())
先把 RFID和 篮筐坐标绑定好，然后
RFID_Buff [index] : hoop_coordinates[index]

if RFID_Buff [index] in key
for key
index++

-----------------------
两个索引，第一个是仓库位置索引， 另一个是篮筐小球索引，用RFID关联起来
rfid_to_location_index = 0
keys = list(rfid_to_location.keys())
for i in range (9)
    idx = RFID_Buff.index(keys(i))
用ID获取其位置索引
'''
'''
lst = ['a', 'b', 'c', 'b']
# 找到 'b' 第一次出现的索引：1
idx = lst.index('b')
'''
# 1. 配置 PB15 为推挽输出

#pin.high()

last_time = pyb.millis()
last_time_ms = pyb.millis()
packet_time_ms = pyb.millis()
def delay_ms(start, tim_ms):
    return pyb.elapsed_millis(start) > tim_ms
angle_180 = [0,0,0,0,0,0] #直接传递给SetMultiServoAngle控制舵机
#--------------------------------------------------
lcd.init()

# -------- 机械臂逆解 --------
H0 = 26.2 #底座高度
L1 = 24.0 #大臂长度
L2 = 21.8 #小臂长度             4
L3 = 11.2 #爪子长度

debugging = 1
def arm_control(x,y,z):
    '''计算底座旋转角度--aqngle_1 '''
    #底座寻转角度 aqngle_1
    if y == 0 and x > 0:
        angle_1 = math.pi* 0.5
    elif y == 0 and x < 0:
        angle_1 = -math.pi*0.5
    elif y<0 and x>0:
        angle_1 = -math.atan(y/x) + math.pi* 0.5
    else:
        angle_1 = math.atan(x/y)

    z_rel = z - H0 #相对底座的高度
    r = math.sqrt(x**2 + y**2) #水平投影距离
    d = math.sqrt(r**2 + z_rel**2)  # 平面二连杆逆解算
    #检查可到达性
    if d > (L1+L2) or d < abs(L1 - L2):
        if d > (L1+L2):
            d = (L1+L2)
        if debugging == 1:
            print("无法到达该位置",d)
        return None

    #小臂旋转角度 aqngle_3-90 逆时针为正
    cos_3 = (L1**2 + L2**2 - d**2) / (2 * L1 *L2)  #得出余弦值
    cos_3 = max(-1.0,min(cos_3,1.0))#约束范围
    angle_3 = math.acos(cos_3)   #反三角计算 小臂 弧度制角度

    #大臂旋转角度 aqngle_2-90 逆时针为正
    alpha = math.atan(z_rel/r) #大臂角2 = 短边 / 投影 弧度制
    beta = math.atan((L2 * math.sin(angle_3)) / (L1 - L2 * math.cos(angle_3)))
    angle_2 = alpha + beta

    angle_out1 = angle_1 / math.pi * 180
    angle_out2 = (angle_2 - math.pi/2)/ math.pi * 180 + 5
    angle_out3 = (angle_3 - math.pi/2)/ math.pi * 180
    return angle_out1,angle_out2,angle_out3   #单位：度

# === 常量（避免拼写错误） ===
POS_HOR = "HOR"     # 水平 horizontal
POS_VER = "VER"     # 垂直 vertical
ACT_OPEN = "OPEN"   # 爪子打开
ACT_CLOSE = "CLOSE" # 爪子闭合

def set_gripper_position(mode_or_angle):
    if mode_or_angle == POS_HOR:
        angle_180[3] = -(angle_180[1] + angle_180[2]) + 7
    elif mode_or_angle == POS_VER:
        angle_180[3] = -(angle_180[1] + angle_180[2]) - 80
    else:
        # 传入数值视为弧度 angle（和你原函数一致）
        angle_180[3] = -(angle_180[1] + angle_180[2]) + (mode_or_angle / math.pi * 180) + 8

def set_gripper_action(action, angle=None):
    if action == ACT_OPEN and angle is not None:
        angle_180[4] = 3-angle
    elif action == ACT_CLOSE:
        angle_180[4] = 3

def set_camera_position(mode_or_angle):
    if mode_or_angle == POS_HOR:
        angle_180[5] = 20
    elif mode_or_angle == POS_VER:
        angle_180[5] = -70
    else:
        angle_180[5] = 20 - mode_or_angle

# -------- 舵机控制 --------
# uart3 --> stm32
# uart1 --> servo
uart_stn32 = UART(3, 115200)
uart_servo = UART(1, 9600)

def angle_transform(angle):
    '''转换角度 '''
    angle_180 = angle
    angles =[0,0,0,0,0,0]
    for i in range(6):
        if i == 0 or i == 2 or i == 4:
            angles[i] = int( (angle_180[i]+135) / 270 *2000 +500)
        else:
            angles[i] = int( (angle_180[i]+90) / 180 *2000 +500)
        # 脉宽限幅
        if angles[i] >=2500:
            angles[i] = 2500
        elif angles[i] <=500:
            angles[i] = 500
    return angles

def SetMultiServoAngle(Holdtime,angle_init):
    '''控制6个舵机 '''
    #将 angle_180 映射到 500--2500
    angles = angle_transform(angle_init)
    # print(angle_init,angles)
    send_data = bytearray(25)
    send_data[0] = 0x55
    send_data[1] = 0x55
    send_data[2] = 23                   # 数据长度 = 3×舵机数 + 5
    send_data[3] = 0x03
    send_data[4] = 0x06                 # 控制 6 个舵机
    send_data[5] = Holdtime & 0xFF
    send_data[6] = (Holdtime >> 8) & 0xFF
    for i in range(6):
        send_data[7 + 3 * i] = i                      # 舵机 ID
        send_data[8 + 3 * i] = angles[i] & 0xFF       # angle 低位
        send_data[9 + 3 * i] = (angles[i] >> 8) & 0xFF  # angle 高位
    uart_servo.write(send_data)                            # 发送数据

#-----------------arm_task------------------
def step_action(x, y, z, g_pos, g_act, g_ang, c_pos, delay_t, hold_t, next_step):
    global arm_step, post_step, platfrom_step, warehouse_step, inbound_step, last_time, task_flag
    if delay_ms(last_time, delay_t+10):  #这里延时的作用是等待上一个动作结束
        res = arm_control(x, y, z)
        if res:
            angle_180[0], angle_180[1], angle_180[2] = res
            set_gripper_position(g_pos)       # 爪子位置
            set_gripper_action(g_act, g_ang)  # 爪子动作
            set_camera_position(c_pos)        # 摄像头位置
            SetMultiServoAngle(hold_t, angle_180)
            last_time = pyb.millis()

            if task_flag == 4:
                post_step = next_step
            elif task_flag == 5:
                warehouse_step = next_step
            elif task_flag == 6:
                inbound_step = next_step
            elif task_flag == 3:
                platfrom_step = next_step
            else:
                arm_step = next_step
# 圆盘机
#  抓点 速度90 step_action(4, 36 - L3 * math.cos(math.asin((5.5) / 11.2)), 48, -math.asin(5.5 / 11.2), ACT_OPEN, 30, 50, 0, 100, 3)
scan_rfid_cnt = 0
def get_ball_disk():
    global color_data, color_state, task_flag, stm32_cmd,last_time_ms, scan_rfid_cnt
    global arm_step, group_index, RFID_Buff_index, RFID_Buff,ID_14_index,packet_time_ms,empty_idx
    if arm_step == 0: step_action(1, 15, 55, POS_HOR, ACT_OPEN, 35, 50, 300, 350, 1)  # 开始过渡动作
    elif arm_step == 100:
        step_action(0, 16, 55, POS_HOR, ACT_OPEN, 45, 50, 300, 200, 1)
        send_cmd_location_buff(0x10, 160)
        last_time_ms = pyb.millis()
    elif arm_step == 1:
        step_action(0, 34 - L3 * math.cos(math.asin(5.5 / 11.2)), 48, POS_HOR, ACT_OPEN, 45, 32, 350, 350, 2)
        time.sleep_ms(350)
        # if delay_ms(last_time_ms, 300):
        #     arm_step =  2
        last_time_ms = pyb.millis()
    elif arm_step == 2:  # 摄像头解算后的点位
        if delay_ms(last_time_ms,15000) == 1:
            print("30s未找到小球，结束任务")
            if ID_14_index is None:
                empty_idx = RFID_Buff_index
            for i in range(6 - RFID_Buff_index):
                RFID_Buff.append(0x00)
                RFID_Buff_index += 1  # 这里可能会影响for 循环
            arm_step = 14
        elif color_data is not None:
            if color_data[0] >= 3500 and color_blob_1 <= 270 and color_blob_1 >= 170:
                step_action(2.5, 36 - L3 * math.cos(math.asin((5.5) / 11.2)), 47.5, -math.asin(5.5 / 11.2), ACT_OPEN, 40, 50, 0, 80, 3)
    elif arm_step == 3: step_action(2.5, 36 - L3 * math.cos(math.asin((5.5) / 11.2)), 47.5, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 80, 40, 4)  # 抓取
    elif arm_step == 4: step_action(1, 15, 50, -math.asin(4.5 / 11.2), ACT_CLOSE, None, POS_VER, 40, 200, 5)  # 过度动作
    elif arm_step == 5: step_action(1, 23.5, 34.2, POS_VER, ACT_CLOSE, None, 50, 200, 400, 6)  # 扫码
    elif arm_step == 20: step_action(1, 22, 50, POS_VER, ACT_CLOSE, None, 50, 400, 400, 5)  #没扫到，回去重扫
    elif arm_step == 6: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 50, 1000, 300, 7)  # 过度
    elif arm_step == 7:
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 300, 300, 8)  # 放
        else:
            scan_rfid_cnt += 1
            if scan_rfid_cnt > 4:  # 扫码4次没扫到，放弃
                RFID_Buff.append(0x00)  # 没扫到，放一个0占位
                RFID_Buff_index = group_index+1
                scan_rfid_cnt = 0
                arm_step = 8
            else:arm_step = 20 #没扫到，重扫
    elif arm_step == 8: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_OPEN, 20, 50, 300, 200, 9)  # 放
    elif arm_step == 9: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_OPEN, 20, 50, 200, 300, 10)  # 上升过渡
    elif arm_step == 10: step_action(1, 10, 50, POS_VER, ACT_OPEN, 20, 50, 300, 400, 11)  # 机械臂回中
    elif arm_step == 11:  #
        scan_rfid_cnt = 0 # 扫到了，清零
        group_index += 1
        if group_index < 6: arm_step = 0  # 下一组
        else:
            print("所有六组放置任务完成")
            send_cmd_location_buff(0x0A, 160)
            time.sleep_ms(2)
            send_cmd_location_buff(0x0A, 160)
            time.sleep_ms(2)
            send_cmd_location_buff(0x0A, 160)
            arm_step = 12  # 停止
    elif arm_step == 12:
        send_cmd_location_buff(0x0A, 160)
        step_action(0, 15, 35, POS_HOR, ACT_OPEN, 38, 38, 400, 400, 12)  # 机械臂回中
    elif arm_step == 14:step_action(1, 6, 55, POS_HOR, ACT_OPEN, 35, 50, 300, 300, 12)
    elif arm_step == 13:
        packet_time_ms = pyb.millis()
        task_flag = 20
        stm32_cmd = 20
        print("结束")


# 阶梯平台  40 60 50 75
def stepped_platfrom():
    global color_data, task_flag, stm32_cmd, last_time_ms, RFID_Buff_index,RFID_Buff
    global platfrom_step, group_index, ball_x, ball_y, stepped_flag,scan_rfid_cnt,empty_idx

    if platfrom_step == 0:
        send_cmd_location_buff(0x30, 160)
        step_action(1, 15, 50, POS_VER, ACT_OPEN, 35, 50, 0, 300, 1)  # 过度动作
    elif platfrom_step == 1:
        send_cmd_location_buff(0x30, 160)
        step_action(1, 10, 60, -math.asin(5.5 / 11.2), ACT_OPEN, 35, 50, 300, 300, 30)  # 过度动作
        last_time_ms = pyb.millis()
    elif platfrom_step == 30:
        step_action(0, 28.5, 58, POS_HOR, ACT_OPEN, 30, 16.5, 300, 400, 30) # 固定观察点位
        # time.sleep_ms(400)
        if delay_ms(last_time_ms, 400):
            platfrom_step = 2
    elif platfrom_step == 2:  # 观察点位 判断阶梯位置 发送小球中心点坐标
        # ============ 判断阶梯位置 ============#
        if color_data[0] >= 5500 and color_data[0] < 9000: stepped_flag = 1    # 中
        elif color_data[0] >= 2600 and color_data[0] < 5500: stepped_flag = 2  # 低
        elif color_data[0] >= 9000: stepped_flag = 3                         # 高
        # ============ 发送小球中心点坐标 ============#
        # if color_data[2] < 190:
        if group_index == 7 :   send_cmd_location_buff(0x0C, color_data[1]) # 抓完第一个球，找第二个球
        elif group_index == 6 : send_cmd_location_buff(0x92, color_data[1]) # 找第一个球

        last_time_ms = pyb.millis()
        if data_rx_stm32 == 0x04 and group_index == 6: platfrom_step = 3 # 抓第一个球
        elif data_rx_stm32 == 0x05: 
            img_txt.draw_string(10, 30, str(color_data[1]), color=(255,255,255), scale=1.6)  # 2倍大小
            platfrom_step = 3                      # 抓第二个球
        elif data_rx_stm32 == 0x0F: # 漏球，结束
            empty_idx = RFID_Buff_index
            for i in range(8 - RFID_Buff_index):
                RFID_Buff.append(0x00)
                RFID_Buff_index += 1
            platfrom_step = 18
    elif platfrom_step == 3: # 到达抓点
        if stepped_flag == 1:   step_action(1, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 45,   -math.asin(5.5 / 11.2), ACT_OPEN, 28, 50, 0, 600, 100)   # 中
        elif stepped_flag == 2: step_action(1, 39 - L3 * math.cos(math.asin(7 / 11.2)),   42, -math.asin(7 / 11.2),   ACT_OPEN, 28, 50, 0, 600, 101) # 低
        elif stepped_flag == 3: step_action(1, 39 - L3 * math.cos(math.asin(5 / 11.2)),   50, -math.asin(5 / 11.2),   ACT_OPEN, 28, 50, 0, 600, 102) # 高
    # 抓球
    elif platfrom_step == 100:  step_action(1, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 45, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 700, 200, 5) # 中
    elif platfrom_step == 101:  step_action(1, 39 - L3 * math.cos(math.asin(7 / 11.2)),   42, -math.asin(7 / 11.2),   ACT_CLOSE, None, 50, 700, 200, 5) # 低
    elif platfrom_step == 102:  step_action(1, 39 - L3 * math.cos(math.asin(5 / 11.2)),   50, -math.asin(5 / 11.2),   ACT_CLOSE, None, 50, 700, 200, 5) # 高
    # 扫码 放入框中
    elif platfrom_step == 5: step_action(1, 5, 60, POS_HOR, ACT_CLOSE, None, 50, 200, 500, 6)
    elif platfrom_step == 6: step_action(1, 23.5, 34.2, POS_VER, ACT_CLOSE, None, 50, 500, 500, 7)
    elif platfrom_step == 40: step_action(1, 18, 48, POS_VER, ACT_CLOSE, None, 50, 400, 400, 6)
    elif platfrom_step == 7:
        openmv_rx_stm32()
        step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 50, 700, 400, 8)
    elif platfrom_step == 8:
        # openmv_rx_stm32()
        # step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 400, 300, 9)
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 400, 300, 9)
        else:
            scan_rfid_cnt += 1
            if scan_rfid_cnt > 3:  # 扫码3次没扫到，放弃
                RFID_Buff.append(0x00)  # 没扫到，放一个0占位
                RFID_Buff_index = group_index+1
                scan_rfid_cnt = 0
                platfrom_step = 9
            else:platfrom_step = 40 #没扫到，重扫
    elif platfrom_step == 9: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_OPEN, 20, 50, 300, 200, 10)
    elif platfrom_step == 10: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_OPEN, 20, 50, 200, 300, 11)
    elif platfrom_step == 11:
        group_index += 1 #  6+1=7 7+1=8
        if group_index < 8: platfrom_step = 0
        else:
            print("阶梯平台抓取结束")
            send_cmd_location_buff(0x0D, 160)
            if ID_14_index is not None: platfrom_step = 12
            else: platfrom_step = 19
    # 抓干扰球
    elif platfrom_step == 12: step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_OPEN, 20, 50, 500, 500, 13)
    elif platfrom_step == 13: step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_OPEN, 24, 50, 500, 300, 14)
    elif platfrom_step == 14: step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 500, 300, 15)
    elif platfrom_step == 15: step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_CLOSE, None, 50, 300, 300, 16)
    elif platfrom_step == 16: step_action(1, 5, 60, POS_HOR, ACT_CLOSE, None, 50, 300, 600, 21)
    elif platfrom_step == 21: step_action(0, 25, 60, POS_HOR, ACT_CLOSE, None, 50, 600, 600, 17)
    # 放干扰球
    elif platfrom_step == 17:
        if stepped_flag == 1:   step_action(0.5, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 46, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 600, 800, 110)   # 中放置点
        elif stepped_flag == 2: step_action(0.5, 39 - L3 * math.cos(math.asin(7 / 11.2)), 43, -math.asin(7 / 11.2),   ACT_CLOSE, None, 50, 600, 800, 111) # 低放置点
        elif stepped_flag == 3: step_action(0.5, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2),   ACT_CLOSE, None, 50, 600, 800, 112) # 高放置点
    elif platfrom_step == 110:  step_action(0.5, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 46, -math.asin(5.5 / 11.2), ACT_OPEN, 25, 50, 800, 150, 18) # 中
    elif platfrom_step == 111:  step_action(0.5, 39 - L3 * math.cos(math.asin(7 / 11.2)), 43, -math.asin(7 / 11.2),   ACT_OPEN, 25, 50, 800, 150, 18) # 低
    elif platfrom_step == 112:  step_action(0.5, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2),   ACT_OPEN, 25, 50, 800, 150, 18) # 高
    elif platfrom_step == 18:   step_action(1, 25, 60, POS_HOR, ACT_OPEN, 25, 50, 400, 600, 22)
    elif platfrom_step == 22:   step_action(1, 5, 60, POS_HOR, ACT_OPEN, 25, 50, 600, 600, 19)
    elif platfrom_step == 19:   step_action(0, 23, 37, POS_VER, ACT_OPEN, 20, 50, 600, 600, 20)
    elif platfrom_step == 20: send_cmd_location_buff(0x0E, 160)

# 立桩
def post_get_ball():
    # 后续可以添加找绿色立桩功能
    post_k = 0.095
    global color_data, post_step, post_x_1, post_y_1, last_time_ms, ball_x, ball_y, group_index, RFID_Buff_index,scan_rfid_cnt,RFID_Buff

    if post_step == 0: step_action(0, 15, 60, POS_HOR, ACT_OPEN, 45, 20, 500, 500, 1)  # 过渡/复位
    elif post_step == 1:
        last_time_ms = pyb.millis()
        step_action(15, 1, 69, POS_HOR, ACT_OPEN, 45, 30, 500, 700, 2)  # 固定观察点 25
    elif post_step == 2:  # 固定观察点 解算坐标
        if delay_ms(last_time_ms, 1500):
            if color_data is not None:
                post_x_0 = (160 - color_data[1]) * post_k # 镜头 x 方向上的偏移 坐标系 y 方向
                post_y_0 = (120 - color_data[2]) * post_k # 镜头 y 方向上的偏移 坐标系 x 方向
                post_x_1 = 31.6 + post_y_0              # 坐标系 x 方向上的距离 28.6 29 30
                post_y_1 = -post_x_0                    # 坐标系 y 方向上的距离
                angle = math.atan(post_y_1 / post_x_1)  # 计算爪子与 坐标系x轴 的夹角的模
                if angle < 0: angle = -angle
                # 爪子在 x , y 方向上的分量
                ball_y = L3 * math.cos(math.asin( 6 / 11.2)) * math.sin(angle)
                ball_x = L3 * math.cos(math.asin( 6 / 11.2)) * math.cos(angle)
                print("post_x_1:", post_x_1, post_y_1, ball_x, ball_y)
                # 计算小臂末端关节的坐标 并补偿
                if post_y_1 < 0:      # 小球在 y轴下方
                    post_x_1 -= ball_x
                    post_y_1 += ball_y
                else:                # 小球在 y轴上方
                    post_x_1 -= ball_x
                    post_y_1 -= ball_y
                # print("color_data:", color_data[0], post_x_1, post_y_1)
                if color_data[0] >= 1000: post_step = 4
            if delay_ms(last_time_ms, 7000): # 超时未找到小球
                group_index = 10
                for i in range(10 - RFID_Buff_index):
                    RFID_Buff.append(0x00)
                    RFID_Buff_index += 1
                post_step = 13
    elif post_step == 4: step_action(post_x_1, post_y_1, 46.3+0.2*(31 - post_x_1), -math.asin( 6 / 11.2), ACT_OPEN, 45, 50, 450, 800, 5)  # 到达抓球点
    elif post_step == 5: step_action(post_x_1, post_y_1, 46.3+0.2*(31 - post_x_1), -math.asin( 6 / 11.2), ACT_CLOSE, None, 50, 900, 200, 6) # 抓球
    elif post_step == 6: step_action(post_x_1-5, post_y_1, 55, -math.asin( 5 / 11.2), ACT_CLOSE, None, 50, 200, 300, 61)  # 抬升
    elif post_step == 61: step_action(0, 15, 60, POS_HOR, ACT_CLOSE, None, 50, 300, 700, 8)  # 抬升
    # elif post_step == 7: step_action(0, 20, 45, POS_HOR, ACT_CLOSE, None, 50, 700, 300, 8)  # 过渡动作
    elif post_step == 8: step_action(1, 23.5, 34.2, POS_VER, ACT_CLOSE, None, 40, 700, 600, 9)  # 扫码
    elif post_step == 40: step_action(1, 23, 45, POS_VER, ACT_CLOSE, None, 40, 300, 400, 8)
    elif post_step == 9: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 40, 1000, 400, 10)  # 放球过渡
    elif post_step == 10: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 400, 300, 11)  # 放
    elif post_step == 11:
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_OPEN, 20, 40, 300, 100, 12)
        else:
            scan_rfid_cnt += 1
            if scan_rfid_cnt > 3:  # 扫码3次没扫到，放弃
                RFID_Buff.append(0x00)  # 没扫到，放一个0占位
                RFID_Buff_index = group_index+1
                scan_rfid_cnt = 0
                post_step = 12
            else:post_step = 40 #没扫到，重扫
    elif post_step == 12: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_OPEN, 20, 40, 150, 200, 13)  # 抬升
    elif post_step == 13: step_action(1, 10, 50, POS_HOR, ACT_OPEN, 20, 40, 300, 500, 14)  # 机械臂回中
    elif post_step == 14:
        group_index += 1
        if group_index < 10: post_step = 0  # 下一组
        else:
            send_cmd_location_buff(0x0F, 160)
            print("立桩任务完成")
            step_action(1, 21, 38, POS_VER, ACT_OPEN, 20, 30, 500, 500, 15)
    elif post_step == 15: send_cmd_location_buff(0x0F, 160)

# ------------- 立体仓库 --------------
ball_data = [] # 1 2 3  分别对应码垛小球编号，根据索引可以判断对应码垛小球的位置
row_num = 0 # 0 1 2  用来记录当前抓取的小球在哪一层
column_cnt = 0     # 0 1 2 对应三个二维码 用来判断小车所处列
img_fps = 0 # 记录满足条件的帧数
curr_x = 0
def warehouse_task():
    index = 0
    global warehouse_step, color_data, packet_time_ms, ball_data, row_num, ID_14_index
    global column_cnt, ID_14_index,empty_idx,data_rx_stm32,qr_rx_buff,curr_x,img_fps
    # ID_14_index = 1  # 默认干扰球在第二列 用于测试
    if len(ball_data) == 1: index = 10  
    else:
        # if ID_14_index is not None: empty_idx = ID_14_index
        if empty_idx is None: empty_idx = ID_14_index
        index = empty_idx

    openmv_rx_stm32()
    #print("状态，收到数据,二维码：",warehouse_step,data_rx_stm32,column_cnt)
    # if data_rx_stm32 == 0xA2 and warehouse_step < 200: warehouse_step = 200  # 最后一列找球超时
    # if data_rx_stm32 == 0x0B: warehouse_step = 90  # 放
    # ============ 第一层 ============ 0 19 1
    if warehouse_step == 0: step_action(0, 5, 55, -math.asin(4/11.2), ACT_OPEN, 35, 70, 400, 400, 19)         #顶层起始##################
    elif warehouse_step == 19:                                                           #观察是否有红色小球
        step_action(0, 14, 57, POS_HOR, ACT_OPEN, 35, 65, 400, 300, 1)                  #顶层观察点#################
        packet_time_ms = pyb.millis()
    elif warehouse_step == 1:       
        if delay_ms(packet_time_ms, 300):                                                     #进去
            if color_data[0] >= 2000 and 1 not in ball_data:                              #有球
                # print("area=",color_data[0])
                img_fps += 1
                if img_fps >= 3:   # 连续三帧满足条件才抓球
                    row_num = 0
                    curr_x = color_data[1]
                    step_action(1+(160-curr_x)*0.02, 20, 56.5, -math.asin(3/11.2), ACT_OPEN, 40, 15, 300, 300, 2)    #################
            else: img_fps = 0
        if delay_ms(packet_time_ms, 1000):                      
            if column_cnt == 0: warehouse_step = 20                                 #第一列 第一层没有球
            elif column_cnt == 1: warehouse_step = 101                                #第二列 第一层没有球
            elif column_cnt == 2:                                                     #第三列 第一层没有球
                if 2 not in ball_data: warehouse_step = 20
                elif 3 not in ball_data: warehouse_step = 30
                else:   # 最后一格没找完
                    warehouse_step = 200
            packet_time_ms = pyb.millis()
    # ============ 第二层 ============ 20 18 21
    elif warehouse_step == 20: step_action(0, 8, 48, POS_HOR, ACT_OPEN, 40, 60, 400, 300, 18) # 中间层过渡动作，防止爪子打到小球 #################
    elif warehouse_step == 18:                                                           #中间过渡动作
        packet_time_ms = pyb.millis()
        step_action(0, 14, 48, -math.asin(2/11.2), ACT_OPEN, 35, 75, 300, 300, 21)       #中间观察点 #################
    elif warehouse_step == 21:
        if delay_ms(packet_time_ms, 300):                                                           #中间抓球点
            if color_data[0] >= 2000 and 2 not in ball_data:                              #有球
                # print("area=",color_data[0])
                img_fps += 1
                if img_fps >= 3:
                    row_num = 1
                    curr_x = color_data[1]
                    step_action(1+(160-curr_x)*0.02, 20, 45, -math.asin(2/11.2), ACT_OPEN, 40, 10, 300, 300, 2)    #################
            else: img_fps = 0
        if delay_ms(packet_time_ms, 3000):                                               #没球
            if column_cnt == 0: warehouse_step = 30                                 #第一列 第二层没有球
            elif column_cnt == 1:
                if 1 not in ball_data: warehouse_step = 0                       #第二列 第一层没有球
                else: warehouse_step = 101
            elif column_cnt == 2:
                if 3 not in ball_data: warehouse_step = 30                      #第三列 第三层没有球
                else:    # 最后一格没找完
                    warehouse_step = 200
            packet_time_ms = pyb.millis()
    # ============ 第三层 ============ 30 17 31
    elif warehouse_step == 30: step_action(0, 6, 37, POS_HOR, ACT_OPEN, 40, 50, 400, 300, 17) # 底层过渡动作，防止爪子打到小球 #################
    elif warehouse_step == 17:
        packet_time_ms = pyb.millis()
        step_action(0, 13, 34, POS_HOR, ACT_OPEN, 30, 65, 300, 300, 31)                  #底层观察点 #################
    elif warehouse_step == 31:
        if delay_ms(packet_time_ms, 300):
            if color_data[0] >= 2000 and 3 not in ball_data:                              #有球
                # print("area=",color_data[0])
                img_fps += 1
                if img_fps >= 3:
                    row_num = 2
                    curr_x = color_data[1]
                    step_action(1+(160-curr_x)*0.02, 20, 32, -math.asin(2/11.2), ACT_OPEN, 40, 50, 300, 300, 2)    #################
            else: img_fps = 0
        if delay_ms(packet_time_ms, 1000):                                               #没球
            if column_cnt == 0: warehouse_step = 100                                #第一列 第三层没有球
            elif column_cnt == 1:
                if 2 not in ball_data: warehouse_step = 20                     #第二列 第二层没有球
                elif 1 not in ball_data: warehouse_step = 0                    #第二列 第一层没有球
                else: warehouse_step = 101                                          #第二列 扫完，一个球没有，剩第三个球
            elif column_cnt == 2:   # 最后一格没找完
                warehouse_step = 200
            packet_time_ms = pyb.millis()
    # ============ 入槽抓球 ============
    elif warehouse_step == 2: #抓球点
        # print("area=",color_data[0])
        if row_num == 0:   step_action(1+(160-curr_x)*0.04, 26, 53, -math.asin(3/11.2), ACT_OPEN, 35, 40, 200, 400, 3)#上
        elif row_num == 1: step_action(1+(160-curr_x)*0.04, 27, 41, -math.asin(4/11.2), ACT_OPEN, 35, 40, 200, 400, 3)#中
        elif row_num == 2: step_action(1+(160-curr_x)*0.04, 27, 28, -math.asin(4/11.2), ACT_OPEN, 35, 40, 200, 400, 3)#下
    elif warehouse_step == 3: #抓球
        if (row_num+1) not in ball_data :
            ball_data.append(row_num+1)
        if row_num == 0:   step_action(1+(160-curr_x)*0.04, 26, 53, -math.asin(3/11.2), ACT_CLOSE, None, 40, 400, 100, 4)#上
        elif row_num == 1: step_action(1+(160-curr_x)*0.04, 27, 41, -math.asin(4/11.2), ACT_CLOSE, None, 40, 400, 100, 4)#中
        elif row_num == 2: step_action(1+(160-curr_x)*0.04, 27, 28, -math.asin(5/11.2), ACT_CLOSE, None, 40, 400, 100, 4)#下
    # ============ 出槽放球 ============
    elif warehouse_step == 4: #入库点
        if row_num == 0:    step_action(1+(160-curr_x)*0.03, 20, 56, -math.asin(3/11.2), ACT_CLOSE, None, 40, 100, 200, 5)#上
        elif row_num == 1:  step_action(1+(160-curr_x)*0.03, 20, 44, -math.asin(2/11.2), ACT_CLOSE, None, 40, 100, 200, 5)#中
        elif row_num == 2:  step_action(1+(160-curr_x)*0.03, 20, 30, -math.asin(2/11.2), ACT_CLOSE, None, 40, 100, 200, 5)           #下  -math.asin(3/11.2)
    elif warehouse_step == 5: #出来
        if row_num == 0:    step_action(1, 14, 57, -math.asin(3/11.2), ACT_CLOSE, None, 40, 200, 200, 6)#上
        elif row_num == 1:  step_action(1, 14, 48, -math.asin(2/11.2), ACT_CLOSE, None, 40, 200, 200, 6)#中
        elif row_num == 2:  step_action(1, 10, 30, -math.asin(1/11.2),            ACT_CLOSE, None, 40, 200, 200, 6)#下
    elif warehouse_step == 6: #过渡动作
        if len(ball_data) < 3:
            step_action(*hoop_coordinates[index * 2], POS_VER, ACT_CLOSE, None, 40, 200, 600, 7)
        else:warehouse_step = 200    #这里不用延时直接跳
    elif warehouse_step ==7:   step_action(*hoop_coordinates[index * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 600, 250, 8)#放
    elif warehouse_step ==8:   step_action(*hoop_coordinates[index * 2 + 1], POS_VER, ACT_OPEN,   25,  40, 250, 100, 9)   #放
    elif warehouse_step == 9:  step_action(*hoop_coordinates[index * 2],     POS_VER, ACT_OPEN,   25,  40, 100, 250, 10)      #过渡动作
    elif warehouse_step == 10: step_action(1, 12, 45, POS_VER, ACT_OPEN, 36, 30, 250, 400, 11)                         #机械臂回中

       # ============ 前面两个小球抓完到这里判断下一个球看哪里 ============
    elif warehouse_step == 11: #
        #if delay_ms(packet_time_ms,500)：
        if column_cnt == 0:                                                              # ============ 第一列 ============#
            if 2 not in ball_data: warehouse_step = 20
            elif 3 not in ball_data: warehouse_step = 30
            if 3 in ball_data and len(ball_data) < 3: warehouse_step = 100       #第三行发现球，但没找到3个
        if column_cnt == 1:                                                                  #第三行抓到球
            if 2 not in ball_data: warehouse_step = 20
            elif 1 not in ball_data: warehouse_step = 0
            else: warehouse_step = 101                                                    #到了最上层
        if column_cnt == 2:                                                                #第一行抓到球
            if 2 not in ball_data: warehouse_step = 20
            elif 3 not in ball_data: warehouse_step = 30
        packet_time_ms = pyb.millis()
    # ============ 右边第一例找完了没找全才会进这里 ============
    elif warehouse_step == 100:                                                           #从这里开始第二列格子
        # if len(qr_rx_buff) in [1, 2]:                                                     #第一列结束
        send_cmd_location_buff(0xA2, 160)                                             #第二列格子开始发送0xA2
        #print("收到：",data_rx_stm32)
        if data_rx_stm32 == 0x08: #这里已经到了中间，并且第一个二维码扫到了才会到这一步                                                    #小车走到中间
            print("第二列格子")
            column_cnt = 1 + column_cnt # 0 + 1 = 1  开始找中间一列                                         #到第二列格子时已经确定了扫到1个二维码
            if 3 not in ball_data: warehouse_step = 30
            elif 2 not in ball_data: warehouse_step = 20
            elif 1 not in ball_data: warehouse_step = 0
            # warehouse_step = 30                                                       #这里已经在观察位了 需要底盘走到这里在发08
        packet_time_ms = pyb.millis()
    # ============ 中间第一例找完了没找全才会进这里 ============
    elif warehouse_step == 101:                                                           #从这里开始第三列格子
        # if len(qr_rx_buff) in [2, 3]:                                                     #第二列结束
        send_cmd_location_buff(0xA3, 160)                                             #第三列格子开始发送0xA3
        #print("收到：",data_rx_stm32)
        if data_rx_stm32 == 0x0A: #这里已经到了 左边                                   #小车走到左边
            print("第三列格子")
            column_cnt = 1 + column_cnt           # 1 + 1 = 2 开始找左边一列
            if 1 not in ball_data: warehouse_step = 0                            #
            elif 2 not in ball_data: warehouse_step = 20
            elif 3 not in ball_data: warehouse_step = 30
        packet_time_ms = pyb.millis()

    # ============ 准备放球 ============
    elif warehouse_step == 200: step_action(0, 5, 50, POS_HOR, ACT_CLOSE, None, 40, 600, 400, 201) #到这里找到三个球了 举球
    elif warehouse_step == 201:  #收到0B入库
        if data_rx_stm32 == 0x08: column_cnt = 1   # 到达中间
        elif data_rx_stm32 == 0x0A: column_cnt = 2 # 到达左边
        if delay_ms(packet_time_ms,1000):  # 等待小车走到放球位置
            if column_cnt== 0:      send_cmd_location_buff(0xA2,160)                          #右边结束发送0xA2
            elif column_cnt== 1:    send_cmd_location_buff(0xA3,160)                          #中间结束发送0xA3
            else:                   send_cmd_location_buff(0xA1,160)                          #左边结束发送0xA1
            packet_time_ms = pyb.millis()

        if data_rx_stm32 == 0x0B:   #等待底盘通知入库 放球
            for i in range(3 - len(ball_data)): ball_data.append(0)  # 没找到的球补0
            step_action(0, 5, 45, POS_HOR, ACT_CLOSE, None, 40, 500, 400, 90)
            time.sleep_ms(410)
    # ============ 码垛放球 ============
    elif warehouse_step == 90:                                                             #起始动作
        if ball_data[2] == 1:   step_action(0, 5,  55, POS_HOR,     ACT_CLOSE, None, 40, 400, 500, 202) #上面
        elif ball_data[2] == 2: step_action(0, 5,  42, POS_HOR,     ACT_CLOSE, None, 40, 400, 500, 202) #中间
        elif ball_data[2] == 3: step_action(0, 11, 34, -math.asin(2/11.2),     ACT_CLOSE,  None, 40, 400, 500, 202) #下面
        else :warehouse_step = 205
    elif warehouse_step == 202:                                                             #入库点
        if ball_data[2] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 203) #上面
        elif ball_data[2] == 2: step_action(0, 27, 42,    -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 203) #中间
        elif ball_data[2] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_CLOSE, None, 40, 500, 600, 203) #下面
    elif warehouse_step == 203:                                                             #放点
        if ball_data[2] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 80) #上面
        elif ball_data[2] == 2: step_action(0, 27, 42,    -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 80) #中间
        elif ball_data[2] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_OPEN, 25, 40, 600, 100, 80) #下面
    elif warehouse_step == 80:                                                              #放球
        if ball_data[2] == 1:   step_action(0, 5,  55,  POS_HOR,            ACT_OPEN, 30,    40, 100, 600, 205) #上面
        elif ball_data[2] == 2: step_action(0, 5,  41,  -math.asin(1/11.2), ACT_OPEN, 30,    20, 100, 600, 205) #中间
        elif ball_data[2] == 3: step_action(0, 5,  31,  -math.asin(4/11.2), ACT_OPEN, 30,    20, 100, 600, 225) #下面

    elif warehouse_step == 225:     step_action(0, 7, 45, POS_HOR, ACT_OPEN, 30, 40, 600, 400, 205) #过渡动作 防止碰撞
    #---------------------第二个球-------------------
    elif warehouse_step == 205:      step_action(*hoop_coordinates[10 * 2], POS_VER, ACT_OPEN, 30, 40, 400, 600, 206)        #篮筐上点位
    elif warehouse_step == 206:      step_action(*hoop_coordinates[10 * 2 + 1], POS_VER, ACT_OPEN, 30, 40, 500, 500, 207)    #篮筐抓点
    elif warehouse_step == 207:      step_action(*hoop_coordinates[10 * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 500, 300, 208) #抓球
    elif warehouse_step == 208:      step_action(*hoop_coordinates[10 * 2], POS_VER, ACT_CLOSE, None, 40, 300, 400, 209)     #篮筐上点位
    # elif warehouse_step == 227:      step_action(0, 5, 45, POS_HOR, ACT_CLOSE, None, 40, 400, 500, 209) #过渡动作 防止碰撞
    elif warehouse_step == 209:                                                             #上升
        if ball_data[0] == 1:   step_action(0, 5,  55, POS_HOR,    ACT_CLOSE, None, 40, 500, 500, 210) #上面
        elif ball_data[0] == 2: step_action(0, 5,  42, POS_HOR,    ACT_CLOSE, None, 40, 500, 500, 210) #中间
        elif ball_data[0] == 3: step_action(0, 11, 34, -math.asin(2/11.2),    ACT_CLOSE, None, 40, 500, 500, 210) #下面
        else :warehouse_step = 213
    elif warehouse_step == 210:                                                             #入库点
        if ball_data[0] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 82) #上面
        elif ball_data[0] == 2: step_action(0, 27, 42,   -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 82) #中间
        elif ball_data[0] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_CLOSE, None, 40, 500, 600, 82) #下面
    elif warehouse_step == 82:                                                              #放球点
        if ball_data[0] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 211) #上面
        elif ball_data[0] == 2: step_action(0, 27, 42,   -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 211) #中间
        elif ball_data[0] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_OPEN, 25, 40, 600, 100, 211) #下面
    elif warehouse_step == 211:                                                             # 放
        if ball_data[0] == 1:   step_action(0, 5,  55, POS_HOR,             ACT_OPEN,  30,   40, 100, 500, 213) #上面
        elif ball_data[0] == 2: step_action(0, 5,  41, -math.asin(1/11.2),  ACT_OPEN,  30,   20, 100, 500, 213) #中间
        elif ball_data[0] == 3: step_action(0, 5,  31, -math.asin(4/11.2),  ACT_OPEN,  30,   20, 100, 500, 226) #下面

    elif warehouse_step == 226:      step_action(0, 7, 45,  POS_HOR,            ACT_OPEN,  30,   40, 500, 400, 213) #过渡动作 防止碰撞
    #-------------------最后一个球------------------
    elif warehouse_step == 213:      step_action(*hoop_coordinates[empty_idx * 2],     POS_VER, ACT_OPEN, 25, 40, 400, 600, 214)        #篮筐上点位
    elif warehouse_step == 214:      step_action(*hoop_coordinates[empty_idx * 2 + 1], POS_VER, ACT_OPEN, 25, 40, 600, 300, 215)    #篮筐抓点
    elif warehouse_step == 215:      step_action(*hoop_coordinates[empty_idx * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 300, 100, 216) #抓球
    elif warehouse_step == 216:      step_action(*hoop_coordinates[empty_idx * 2],     POS_VER, ACT_CLOSE, None, 40, 100, 300, 224)     #篮筐上点位
    # elif warehouse_step == 217:      step_action(0, 5,  45,  POS_HOR, ACT_CLOSE, None, 40, 300, 500, 224) #
    elif warehouse_step == 224:                                                             #
        if ball_data[1] == 1:   step_action(0, 5,  55,  POS_HOR, ACT_CLOSE, None, 40, 500, 500, 84) #上面
        elif ball_data[1] == 2: step_action(0, 5,  42,  POS_HOR, ACT_CLOSE, None, 40, 500, 500, 84) #中间
        elif ball_data[1] == 3: step_action(0, 11, 34,  -math.asin(2/11.2), ACT_CLOSE, None, 40, 500, 500, 84) #下面
        else :warehouse_step = 223
    elif warehouse_step == 84:                                                              #入点
        if ball_data[1] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 218) #上面
        elif ball_data[1] == 2: step_action(0, 27, 42,    -math.asin(1/11.2), ACT_CLOSE, None, 40, 500, 600, 218) #中间
        elif ball_data[1] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_CLOSE, None, 40, 500, 600, 218) #下面
    elif warehouse_step == 218:                                                             #放点
        if ball_data[1] == 1:   step_action(0, 25, 53.5, -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 219) #上面
        elif ball_data[1] == 2: step_action(0, 27, 41,   -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 100, 219) #中间
        elif ball_data[1] == 3: step_action(0, 27, 30,   -math.asin(4/11.2), ACT_OPEN, 25, 40, 600, 100, 219) #下面
    elif warehouse_step == 219:                                                             #  放
        if ball_data[1] == 1:   step_action(0, 5,  55,   POS_HOR, ACT_OPEN,  30,   40, 100, 500, 223) #上面
        elif ball_data[1] == 2: step_action(0, 5,  41,   -math.asin(2/11.2), ACT_OPEN,  30,   20, 100, 500, 223) #中间
        elif ball_data[1] == 3: step_action(0, 5,  31,   -math.asin(4/11.2), ACT_OPEN,  30,   20, 100, 500, 223) #下面

    elif warehouse_step == 223:                                                             #出来 这个阶段完成，发送0xA4
        step_action(0, 20, 39, POS_VER, ACT_OPEN, 30, 40, 500, 300, 223)
        send_cmd_location_buff(0xA4,160)


# ============ 入库 ============#
def inbound_storage():
    global RFID_Buff, rfid_to_location, hoop_coordinates, inbound_index, idx, keys, inbound_step
    # print(inbound_index, idx, inbound_step) #仓库位置索引 对应篮筐位置 入库步骤
    # img_txt.clear()
    # img_txt.draw_string(10, 10, "step:", color=(255,255,255), scale=1.5)  # 2倍大小
    # img_txt.draw_string(80, 10, str(inbound_step), color=(255,255,255), scale=1.5)  # 2倍大小
    # lcd.display(img_txt)
    if inbound_step == 0:                                                                 #开始过渡动作+
        # 获取 keys 中每一个值在 RFID_Buff 中的索引 也对应了篮筐中的索引
        if keys[inbound_index] in RFID_Buff and RFID_Buff.index(keys[inbound_index]) is not None:
            idx = RFID_Buff.index(keys[inbound_index])
            step_action(*hoop_coordinates[idx * 2], POS_VER, ACT_OPEN, 25, 40, 400, 500, 1)
        else:
            inbound_index += 1
            if inbound_index < 9: inbound_step = 0
            else: inbound_step = 9
            # idx = 10
    elif inbound_step == 1: step_action(*hoop_coordinates[idx * 2 + 1], POS_VER, ACT_OPEN, 25, 40, 500, 400, 2) #到抓球点
    elif inbound_step == 2: step_action(*hoop_coordinates[idx * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 500, 300, 3) #抓球
    elif inbound_step == 3: step_action(*hoop_coordinates[idx * 2], POS_VER, ACT_CLOSE, None, 30, 300, 300, 20) #抬升
    elif inbound_step == 20: step_action(0, 12, 40, POS_VER, ACT_CLOSE, None, 40, 300, 400, 4) #机械臂回中
    elif inbound_step == 4:                                                               #放球中间动作
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][0], POS_HOR, ACT_CLOSE, None, 40, 400, 600, 5)
        else: step_action(*rfid_to_location[keys[inbound_index]][0], -math.asin(4/11.2), ACT_CLOSE, None, 40, 350, 600, 5)
    elif inbound_step == 5:                                                               #放球点
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(1/11.2), ACT_CLOSE, None, 40, 600, 600, 6)
        else: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(4/11.2), ACT_CLOSE, None, 40, 600, 600, 6)
    elif inbound_step == 6:                                                               #放球
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(1/11.2), ACT_OPEN, 25, 40, 600, 200, 7)
        else: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(4/11.2), ACT_OPEN, 25, 40, 600, 200, 7)
    elif inbound_step == 7:                                                               #退回
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][0], POS_HOR, ACT_CLOSE, None, 40, 200, 600, 8) #上面两行
        else: step_action(*rfid_to_location[keys[inbound_index]][0], -math.asin(4/11.2), ACT_CLOSE, None, 30, 200, 600, 8) #最下面一行
    elif inbound_step == 8:                                                               #
        inbound_index = 1 + inbound_index
        if inbound_index < 9: inbound_step = 0
        else: inbound_step = 9
    elif inbound_step == 9: step_action(0, 23, 38, POS_VER, ACT_CLOSE, None, 30, 600, 600, 10) #机械臂回中
    elif inbound_step == 10: send_cmd_location_buff(0xA5, 160)                            #

# ============ 通信 ============
def openmv_rx_stm32():
    global task_flag,data_rx_stm32,qr_rx_buff,keys
    global RFID_Buff,ID_14_index,RFID_Buff_index,warehouse_threshold
    # print("5")
    re_list_stm32 = []
    if uart_stn32.any():
        data = uart_stn32.read()
        # print("从stm32收到的数据：",data)
        if data:
            # print("收到十六进制:", ' '.join(f'{b:02X}' for b in data))
            re_list_stm32.extend(data)  # 将接收到的数据添加到列表中
            if len(re_list_stm32) >= 3:
                # print("收到十六进制:", ' '.join(f'{b:02X}' for b in re_list_stm32))
                # 任务调度指令
                if re_list_stm32[0] == 0xAB and re_list_stm32[2] == 0xEF:
                    re_cmd = re_list_stm32[1]  # 提取命令字节
                    # print("re_cmd:",re_cmd)
                    if re_cmd == 1:    task_flag = 1 # 圆盘机
                    elif re_cmd == 2:  task_flag = 2 # 避障
                    elif re_cmd == 3 : task_flag = 3 # 阶梯平台
                    elif re_cmd == 6 : task_flag = 4 # 立桩
                    elif re_cmd == 7 or re_cmd == 0x0D:# 码垛
                        if re_cmd == 0x0D: # 固定入库顺序，用于测试
                            warehouse_threshold = blue_threshold_warehouse
                            ID_14_index = 1  # 默认干扰球在第二列 用于测试
                        task_flag = 5
                    elif re_cmd == 0x0C or re_cmd == 0x0E :# 入库
                        if re_cmd == 0x0E: # 固定入库顺序，用于测试
                            RFID_Buff = keys.copy()
                            qr_rx_buff = [0x31,0x32,0x33]
                        task_flag = 6
                    data_rx_stm32 = re_cmd
                    #print(task_flag)
                    return re_cmd
                #读卡器
                elif re_list_stm32[0] == 0x55 and re_list_stm32[2] == 0x66:
                    if re_list_stm32[1] not in RFID_Buff and re_list_stm32[1] in keys:
                        send_cmd_location_buff(re_list_stm32[1],160)
                        if re_list_stm32[1] == 0x14:
                            ID_14_index = RFID_Buff_index
                        RFID_Buff.append((re_list_stm32[1]))
                        RFID_Buff_index = RFID_Buff_index+1
                    print("RFID:",re_list_stm32[1])
                    # print(RFID_Buff)
                    return re_list_stm32[1]
                #二维码
                elif re_list_stm32[0] == 0x77 and re_list_stm32[2] == 0x88:
                    if re_list_stm32[1] not in qr_rx_buff and re_list_stm32[1] in [0x31,0x32,0x33] and qr_rx_buff[column_cnt] == 0:
                        qr_rx_buff[column_cnt] = re_list_stm32[1] #这里 32 扫到二维码才会发过来，不会出现发送上一次数据的情况
                        # send_cmd_location_buff(re_list_stm32[1],160)
                        # qr_rx_buff.append(re_list_stm32[1]) #例如：0x31-0x20==0x11
                    # print("qr_rx_buff:",len(qr_rx_buff))
                    #print(qr_rx_buff)
                    return re_list_stm32[1]
                re_list_stm32.clear()  # 清空数据列表，准备接收下一个包
    else :
        return None

#和STM32通信
# 发送数据包的函数
def send_data_packet(data):
    payload = bytearray(data)
    data_packet = bytearray([0xBB]) + bytearray([0x99]) + payload + bytearray([0xFF])
    uart_stn32.write(data_packet)
    #print("发送数据包:", data)
#发坐标
def send_pozation(data):
    data1 = data & 0xFF
    data2 = (data >> 8) & 0xFF
    uart_stn32.write(bytes([0xAA,data1,data2,0xEE]))
    # print("发送坐标:", data)

def send_cmd_location_buff(cmd,location):
    data1 = location & 0xFF
    data2 = (location >> 8) & 0xFF
    uart_stn32.write(bytes([0x77,cmd,data1,data2,0x88]))
    # print("发送：",cmd,location)
    time.sleep_us(500)

disk_threshold = (45, 97, 54, 90, -14, 75)
stepped_platfrom_threshold = (45, 97, 54, 90, -14, 75)
post_threshold = (30, 100, 15, 127, -20, 127)
warehouse_threshold = (30, 100, 15, 127, -20, 127)
def chose_ball_color():
    global disk_threshold,stepped_platfrom_threshold,post_threshold,warehouse_threshold
    if data_rx_stm32 == 0xA3:
        disk_threshold = red_threshold
        stepped_platfrom_threshold = red_threshold_stepplatfrom
        post_threshold = red_threshold_warehouse
        warehouse_threshold = red_threshold_warehouse
    elif data_rx_stm32 == 0xA4:
        disk_threshold = blue_threshold
        stepped_platfrom_threshold = blue_threshold_stepplatfrom
        post_threshold = blue_threshold_post
        warehouse_threshold = blue_threshold_warehouse

def chose_ball_blue():
    global disk_threshold,stepped_platfrom_threshold,post_threshold,warehouse_threshold
    disk_threshold = blue_threshold_post
    # disk_threshold = blue_threshold
    # stepped_platfrom_threshold = blue_threshold_stepplatfrom
    # post_threshold = blue_threshold_post
    # warehouse_threshold = blue_threshold_warehouse

def chose_ball_red():
    global disk_threshold,stepped_platfrom_threshold,post_threshold,warehouse_threshold
    disk_threshold = red_threshold
    stepped_platfrom_threshold = red_threshold_stepplatfrom
    post_threshold = red_threshold_warehouse
    warehouse_threshold = red_threshold_warehouse

def search_ball():
    global task_flag,color_blob_1
    area = 0
    if task_flag == 5:    my_threshold = warehouse_threshold # 码垛
    elif task_flag == 3:  my_threshold = stepped_platfrom_threshold # 阶梯平台
    elif task_flag == 4:  my_threshold = post_threshold  # 立桩
    else :                my_threshold = disk_threshold  # 圆盘机

    if task_flag == 1:   my_roi = DISKROI
    elif task_flag == 3: my_roi = stepplatfrom_roi
    else:                my_roi = ROI
    img = sensor.snapshot().lens_corr(1.2)
    #img.draw_rectangle(stepplatfrom_roi)
    img.draw_cross(160, 120)
    openmv_rx_stm32()
    blobs = img.find_blobs([my_threshold],roi = my_roi , pixels_threshold=500, area_threshold=1000, merge=True)
    if blobs :
        for blob in blobs:
            x = blob[0]
            y = blob[1] #
            width = blob[2]
            height = blob[3]
            color_blob_1 = x
            #print("w,h:",width,height)
            # perimeter = float(blob.perimeter()) #周长像素点个数
            area = float(blob.area())
            img.draw_string(blob.cx(),blob.cy(), "red", color = (0xFF, 0x00, 0x00))
            img.draw_rectangle([x, y, width, height])
            img.draw_cross(blob.cx(), blob.cy())
            # lcd.display(img)
            # print("area=",area,blob.cx(), blob.cy())
            return area,blob.cx(),blob.cy()
    else :
        openmv_rx_stm32()
        # lcd.display(img)
        #print("area=",area)
        return 0,0,0

def search_white():
    global is_send_data,task_flag
    openmv_rx_stm32()
    img = sensor.snapshot().lens_corr(1.2)  # 每次拍新图
    img.draw_rectangle(ROI)

    if delay_ms(packet_time_ms,3500): # 没找到白色就复位发送标志
        send_cmd_location_buff(0x0B,160)
        send_cmd_location_buff(0x0B,160)
        step_action(1, 20, 38, POS_VER, ACT_OPEN, 25, 40, 0, 300, 1)

    #pixels_threshold 最低像素点  area_threshold  最低面积 长*宽 merge=True 如果多个相邻的 blobs 符合条件，会把它们合并成一个大的 blob
    blobs = img.find_blobs([white_threshold],roi = ROI , pixels_threshold=500, area_threshold=1000, merge=True)
    if blobs :
        for blob in blobs:
            x = blob[0]
            y = blob[1] #
            width = blob[2]
            height = blob[3]
            area = float(blob.area())
            # print("area:",area)
            if area>= 6000 : #and is_send_data == 1
                send_cmd_location_buff(0x0B,160)
                time.sleep_ms(2)
                send_cmd_location_buff(0x0B,160)
                step_action(1, 20, 38, POS_VER, ACT_OPEN, 25, 40, 0, 300, 1)
            else :
                send_cmd_location_buff(0x20,160)
                time.sleep_ms(2)
                send_cmd_location_buff(0x20,160)
            img.draw_string(blob.cx(),blob.cy(), "white", color = (0xFF, 0x00, 0x00))
            img.draw_rectangle([x, y, width, height])
            img.draw_cross(blob.cx(), blob.cy())
            # lcd.display(img)
            return area,x,y
    else :
        send_cmd_location_buff(0x20,160)
        #send_data_packet([0x20])
        # lcd.display(img)
        # video.record(img, clock.fps()) # 录制视频
        return 0,0,0
img_txt = image.Image(160, 80, image.RGB565)      # 可以指定尺寸

while True:
    clock.tick()
    # img_txt.clear()
    # img_txt.draw_string(10, 30, "qr:", color=(255,255,255), scale=1.5)
    # img_txt.draw_string(80, 30, str(len(qr_rx_buff)), color=(255,255,255), scale=1.5)  # 2倍大小
    # lcd.display(img_txt)
    # search_ball()
    # search_white()
    #---------------------------------------------------------------
    if flag == 1 :#7500 17160 4000
        enter = 1
        send_cmd_location_buff(0x51,160)
        if arm_step == 0:   step_action(0,23,36, POS_VER, ACT_CLOSE, None, 50, -10, 600, 1)
        elif arm_step == 1: step_action(0,12,45, POS_VER, ACT_OPEN, 35, 50, 600, 600, 3) #
        elif arm_step == 2: step_action(0, 14, 57, POS_HOR, ACT_OPEN, 35, 65, 600, 600, 3)
        elif arm_step == 3:
            arm_step = 0
            # step_action(0,12,45, POS_VER, ACT_CLOSE, None, 50, -10, 300, 0)
            flag = 0
        # ============ 测平台抓取和放球 ============#  180 210 
        elif arm_step == 4: step_action(1, 15, 50, POS_VER, ACT_OPEN, 35, 50, 500, 300, 5)
        elif arm_step == 5: step_action(1, 10, 60, POS_HOR, ACT_OPEN, 35, 50, 300, 300, 6)
        elif arm_step == 6: step_action(1, 28.5, 58, POS_HOR, ACT_OPEN, 20, 16.5, 300, 500, 3)
        # ============ 测高平台抓取和放球 ============#
        # elif arm_step == 7: step_action(0, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2), ACT_OPEN, 25, 50, 500, 500, 8)
        # elif arm_step == 8: step_action(0, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2),ACT_CLOSE, None, 50, 500, 200, 9)
        #  # ============ 测中平台抓取和放球 ============#
        elif arm_step == 7: step_action(0, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 45, -math.asin(5.5 / 11.2), ACT_OPEN, 25, 50, 500, 600, 8)
        elif arm_step == 8: step_action(0, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 45, -math.asin(5.5 / 11.2),ACT_CLOSE, None, 50, 600, 200, 9)
        #  # ============ 测低平台抓取和放球 ============#
        # elif arm_step == 7: step_action(0, 39 - L3 * math.cos(math.asin(7 / 11.2)), 42, -math.asin(7 / 11.2), ACT_OPEN, 25, 50, 500, 600, 8)
        # elif arm_step == 8: step_action(0, 39 - L3 * math.cos(math.asin(7 / 11.2)), 42, -math.asin(7 / 11.2),ACT_CLOSE, None, 50, 600, 200, 9)
        elif arm_step == 9: step_action(1, 5, 60, POS_HOR, ACT_CLOSE, None, 50, 200, 400, 10)
        elif arm_step == 10: step_action(1, 23.5, 35, POS_VER, ACT_CLOSE, None, 50, 400, 500, 11)
        elif arm_step == 11: step_action(*hoop_coordinates[0 * 2], POS_VER, ACT_OPEN, 20, 50, 500, 500, 12)
        elif arm_step == 12: step_action(*hoop_coordinates[0 * 2 + 1], POS_VER, ACT_OPEN, 24, 50, 500, 300, 13)
        elif arm_step == 13: step_action(*hoop_coordinates[0 * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 500, 300, 14)
        elif arm_step == 14: step_action(1, 5, 60, POS_HOR, ACT_CLOSE, None, 50, 300, 400, 100)
        elif arm_step == 100: step_action(1, 25, 60, POS_HOR, ACT_CLOSE, None, 50, 400, 600, 15)
        # ============ 测高平台抓取和放球 ============#
        # elif arm_step == 15: step_action(0, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2), ACT_CLOSE, None, 50, 600, 500, 16)
        # elif arm_step == 16: step_action(0, 39 - L3 * math.cos(math.asin(5 / 11.2)), 50, -math.asin(5 / 11.2), ACT_OPEN, 25, 50, 500, 250, 101) # 高
         # ============ 测中平台抓取和放球 ============#
        elif arm_step == 15: step_action(0, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 46, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 600, 600, 16)
        elif arm_step == 16: step_action(0, 39 - L3 * math.cos(math.asin(5.5 / 11.2)), 46, -math.asin(5.5 / 11.2), ACT_OPEN, 30, 50, 600, 250, 17) # 高
        # ============ 测低平台放球 ============#
        # elif arm_step == 15: step_action(1.5, 39 - L3 * math.cos(math.asin(7 / 11.2)), 43, -math.asin(7 / 11.2), ACT_CLOSE, None, 50, 600, 600, 16)
        # elif arm_step == 16: step_action(1.5, 39 - L3 * math.cos(math.asin(7 / 11.2)), 43, -math.asin(7 / 11.2), ACT_OPEN, 30, 50, 600, 250, 17) # 高
        elif arm_step == 101: step_action(1, 25, 60, POS_HOR, ACT_CLOSE, None, 50, 400, 600, 17)
        elif arm_step == 17: step_action(1, 5, 60, POS_HOR, ACT_OPEN, 25, 50, 500, 400, 18)
        elif arm_step == 18: step_action(0, 23, 37, POS_VER, ACT_OPEN, 20, 40, 600 , 600, 3)
        # # ============ 测立桩 ============#
        # elif arm_step == 4: step_action(0, 15, 60, POS_HOR, ACT_OPEN, 45, 20, 500, 500, 5)
        # elif arm_step == 5: step_action(10, 1, 60, POS_HOR, ACT_OPEN, 30, 20, 400, 300, 6)
        # elif arm_step == 6: step_action(15, 1, 69, POS_HOR, ACT_OPEN, 45, 25, 300, 600, 3)
    #---------------------------------------------------------------
    stm32_cmd = openmv_rx_stm32() #接收CMD
    chose_ball_color()
    # chose_ball_blue()
    # chose_ball_red()
    # pin = pyb.Pin(pyb.Pin.cpu.B15, pyb.Pin.OUT_PP)
    # pin.low()
    # print("2")
    if task_flag == 1:# 圆盘机
        color_data = search_ball()
        get_ball_disk()
        packet_time_ms = time.ticks_ms()
    elif task_flag == 2:# 避障
        white_data = search_white()
        # print("area:",white_data[0])
    elif task_flag == 3:# 阶梯平台
        img_txt.clear()
        img_txt.draw_string(10, 10, "x:", color=(255,255,255), scale=1.5)
        
        lcd.display(img_txt)
        if flag == 0 :
            group_index = 6
            # RFID_Buff_index = 6
            flag = 2
        color_data = search_ball()
        stepped_platfrom()

    elif task_flag == 4:# 立桩
        if flag == 2 :
            group_index = 8
            flag = 3
        color_data = search_ball()
        post_get_ball()
    elif task_flag == 5:# 码垛
        # pin = pyb.Pin(pyb.Pin.cpu.B15, pyb.Pin.OUT_PP)
        # pin.low()
        # img_txt.clear()
        # img_txt.draw_string(10, 10, "qr:", color=(255,255,255), scale=1.5)
        # img_txt.draw_string(10, 30, str(qr_rx_buff), color=(255,255,255), scale=1.6)  # 2倍大小
        # lcd.display(img_txt)
        #print(warehouse_step,ball_data)
        color_data = search_ball()
        #send_cmd_location_buff(warehouse_step,160) #第二列格子开始发送0xA2
        warehouse_task()
    elif task_flag == 6:# 入库
        # img_txt.clear()
        # img_txt.draw_string(10, 10, "qr:", color=(255,255,255), scale=1.5)
        # img_txt.draw_string(10, 30, str(qr_rx_buff), color=(255,255,255), scale=1.6)  # 2倍大小
        # lcd.display(img_txt)
        if enter == 1:
            send_cmd_location_buff(0xCC,160)
            for i in range(3):
                if qr_rx_buff[i] == 0:
                    qr_rx_buff[i] = 0x96 - (qr_rx_buff[0] + qr_rx_buff[1] + qr_rx_buff[2]) # 31 32 33
            # if len(qr_rx_buff) == 2: qr_rx_buff.append(0x96 - (qr_rx_buff[0] + qr_rx_buff[1])) # 31 32 33
            # elif len(qr_rx_buff) == 1:
            #     for i in range(3 - len(qr_rx_buff)):
            #         qr_rx_buff.append(0x00) #补齐三个位置
            qr_to_loocation()
            print("ok")
            print(" 读取的 ID :",RFID_Buff)
            print(" 读取的 二维码 :",qr_rx_buff)
            inbound_index = 0
            enter = 4
        inbound_storage()
        #print(keys)
    else:
        # print("3")
        if data_rx_stm32  == 0x0C:
            send_cmd_location_buff(0x0C,160)
    #print(qr_rx_buff , RFID_Buff)
    time.sleep_ms(2)
    # print("4")
