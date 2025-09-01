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
#(26, 80, -38, 42, -105, -42)
red_threshold = (45, 97, 54, 90, -14, 75)
blue_threshold = (30, 82, -37, 39, -66, -36) #(23, 73, -8, 45, -87, -47)  # (39, 85, -64, 60, -87, -13) # (38, 71, -7, 45, -87, -47) #
blue_threshold_warehouse = (18, 78, -38, 51, -82, -27)
white_threshold = (65, 96, -32, 71, -13, 47)
#颜色码
red_color_code = 1
blue_color_code = 2
green_color_code = 4
white_color_code = 8
yellow_color_code = 16

ROI = (0,0,320,240)

stepplatfrom_roi = (0,0,320,170)

DISKROI = (0,0,320,150)
WHITEROI = (70,0,200,90)
red_data = []
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
#篮筐坐标
hoop_coordinates = [[13,20,38]   , [13,21,33.0] ,  #0
                    [7, 20, 38]  , [7, 21.5, 32.6],
                    [-6, 20, 38] , [-6, 21.5, 32.6],
                    [-12,20,38] , [-12,21.5,32.6],
                    # Second row
                    [-13,14.5,38.5]    ,  [-13,14.5,33],
                    [-5.5,14.5,38.5]  ,  [-5.5,14.5,33],
                    [0,12,38]     ,  [0,13.6,33.5] ,
                    [6,12,38.5]    ,  [6,14,33] ,
                    [12,13.3,38.5]   ,  [12,14,33] ,
                    #Third row
                    [13,7.5,38.5]     ,  [13,7.5,33] ,
                    [-13.5,7.5,38]  ,  [-13.5,7.5,33], #10 共11个
                    ]
group_index = 0
RFID_Buff = []  #接收stm32读取的RFID
RFID_Buff_index = 0
ID_14_index = None
#-----------------摄像头扫码-----------
qr_result = []
last_qr_result = None
#-------------扫码模块--------------------
qr_rx_buff = []
qr_rx_buff_last = None
#------------RFID和仓库坐标---------------
inbound_index = 0 #仓库位置索引
idx = 0 #对应篮筐位置索引
keys = [0x31,0x32,0x33,0x21,0x22,0x23,0x11,0x12,0x13]
#仓库位置坐标
rfid_to_location = {
    #最上面第三行
    0x31 : ([7,14,55] , [14,29,53.3]),
    0x32 : ([0,12,56] , [0,29,54]),
    0x33 : ([-7,14,56] , [-14,29,54]),
    #中间一行
    0x21 : ([7,14,44] , [14,29,42]),
    0x22 : ([0,14,44] , [0,29,42]),
    0x23 : ([-7,14,44] , [-14,29,42]),
    #第一行
    0x11 :([7,12,31.5] , [14,24,30.3]), #([7,12,32.5] , [14,24,32.5]),
    0x12 : ([0,12,30.5] , [0,24,31]),  #([0,12,32.5] , [0,24,32.5]),
    0x13 : ([-7,12,31.5] , [-13,24,31]),  #([-7,12,32.5] , [-13,24,32.5]),
    #后面修改可以这样 ：3
    # rfid_to_location[0x11] = ([7,12,32.5], [14,24,32.5])
}
#利用二维码补充立体仓库货架位置  现在位置都有了，可以写搬运动作了
def qr_to_loocation():
    global qr_rx_buff,rfid_to_location
    if qr_rx_buff[0] == 0x33:
        rfid_to_location[0x13] = ([-7,14,32] , [-14,29,31])
    elif qr_rx_buff[0] == 0x32:
        rfid_to_location[0x12] = ([-7,14,32] , [-14,29,31])
    elif qr_rx_buff[0] == 0x31:
        rfid_to_location[0x11] = ([-7,14,32] , [-14,29,31])

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
    print(rfid_to_location[0x11])
    print(rfid_to_location[0x12])
    print(rfid_to_location[0x13])
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
#pin = pyb.Pin(pyb.Pin.cpu.B15, pyb.Pin.OUT_PP)
#pin.low()
#pin.high()

last_time = pyb.millis()
last_time_ms = pyb.millis()
packet_time_ms = pyb.millis()
def delay_ms(start, tim_ms):
    return pyb.elapsed_millis(start) > tim_ms
angle_180 = [0,0,0,0,0,0] #直接传递给SetMultiServoAngle控制舵机
#--------------------------------------------------
# lcd.init()

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
        angle_180[4] = -angle
    elif action == ACT_CLOSE:
        angle_180[4] = 0

def set_camera_position(mode_or_angle):
    if mode_or_angle == POS_HOR:
        angle_180[5] = 15
    elif mode_or_angle == POS_VER:
        angle_180[5] = -75
    else:
        angle_180[5] = 15 - mode_or_angle

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

def SetServoAngle(ID, Holdtime, angle):
    '''控制单个舵机 '''
    send_data = bytearray(10)
    send_data[0] = 0x55
    send_data[1] = 0x55
    send_data[2] = 8
    send_data[3] = 0x03
    send_data[4] = 0x01
    send_data[5] = Holdtime & 0xFF           # Holdtime 低八位
    send_data[6] = (Holdtime >> 8) & 0xFF    # Holdtime 高八位
    send_data[7] = ID
    send_data[8] = angle & 0xFF          # angle 低八位
    send_data[9] = (angle >> 8) & 0xFF   # angle 高八位
    uart_servo.write(send_data)            # 发送数据

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
scan_rfid_cnt = 0
def get_ball_disk():
    global red_data, color_state, task_flag, stm32_cmd,last_time_ms, scan_rfid_cnt
    global arm_step, group_index, RFID_Buff_index, RFID_Buff
    if arm_step == 0: step_action(1, 6, 55, POS_HOR, ACT_OPEN, 35, 50, 300, 300, 100)  # 开始过渡动作
    elif arm_step == 100: step_action(1, 16, 55, POS_HOR, ACT_OPEN, 35, 50, 300, 200, 1)
    elif arm_step == 1:
        send_cmd_location_buff(0x10, 160)
        step_action(0, 34 - L3 * math.cos(math.asin(5.5 / 11.2)), 48, POS_HOR, ACT_OPEN, 35, 32, 200, 350, 2)  # 固定观察点位 (要改)
        last_time_ms = pyb.millis()
    elif arm_step == 2:  # 摄像头解算后的点位
        if delay_ms(last_time_ms,25000) == 1:
            print("30s未找到小球，结束任务")
            arm_step = 12
        if red_data is not None:
            if red_data[0] >= 3000 and color_blob_1 <= 260 and color_blob_1 >= 170:
                step_action(2, 34 - L3 * math.cos(math.asin((47 - 41.5) / 11.2)), 47, -math.asin(4.5 / 11.2), ACT_OPEN, 30, 50, 200, 100, 3)
    elif arm_step == 3: step_action(2, 32 - L3 * math.cos(math.asin((47 - 41.5) / 11.2)), 50, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 100, 100, 4)  # 抓取
    elif arm_step == 4: step_action(1, 10, 50, -math.asin(4.5 / 11.2), ACT_CLOSE, None, POS_VER, 100, 200, 5)  # 过度动作
    elif arm_step == 5: step_action(1, 23.5, 35, POS_VER, ACT_CLOSE, None, 50, 200, 400, 6)  # 扫码
    elif arm_step == 20: step_action(1, 22, 50, POS_VER, ACT_CLOSE, None, 50, 400, 400, 5)  #没扫到，回去重扫
    elif arm_step == 6: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 50, 1000, 300, 7)  # 过度
    elif arm_step == 7:
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 300, 300, 8)  # 放
        else:
            scan_rfid_cnt += 1
            if scan_rfid_cnt > 3:  # 扫码5次没扫到，放弃
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
        step_action(0, 15, 35, POS_HOR, ACT_OPEN, 35, 30, 400, 300, 12)  # 机械臂回中
    elif arm_step == 13:
        task_flag = 20
        stm32_cmd = 20
        print("结束")


# 阶梯平台  40 60 50 75
def stepped_platfrom():
    global red_data, task_flag, stm32_cmd, last_time_ms, RFID_Buff_index
    global platfrom_step, group_index, ball_x, ball_y, stepped_flag
    if platfrom_step == 0:
        send_cmd_location_buff(0x30, 160)
        step_action(1, 15, 50, POS_VER, ACT_OPEN, 35, 50, 500, 300, 1)  # 过度动作
    elif platfrom_step == 1:
        send_cmd_location_buff(0x30, 160)
        step_action(1, 10, 60, -math.asin(5.5 / 11.2), ACT_OPEN, 35, 50, 300, 500, 2)  # 过度动作
    elif platfrom_step == 2:  # 观察点位 判断阶梯位置 发送小球中心点坐标
        step_action(0, 28.5, 58, POS_HOR, ACT_OPEN, 20, 16.5, 500, 500, 2) # 固定观察点位
        if red_data[0] >= 5500 and red_data[0] < 9000: stepped_flag = 1    # 中
        elif red_data[0] >= 3000 and red_data[0] < 5500: stepped_flag = 2  # 低
        elif red_data[0] >= 9000: stepped_flag = 3                         # 高
        if delay_ms(last_time_ms, 30):
            if group_index == 7 and red_data[1] <= 130: send_cmd_location_buff(0x0C, red_data[1])  #发送小球位置
            elif red_data[1] <= 163 and red_data[1] >= 157:  # 小球位置在中间
                if group_index == 1: send_cmd_location_buff(0x0D, red_data[1])
                else: send_cmd_location_buff(0x91, red_data[1])
            else: send_cmd_location_buff(0x92, red_data[1])
            last_time_ms = pyb.millis()
        openmv_rx_stm32()
        if data_rx_stm32 == 0x04 and group_index == 6: platfrom_step = 3
        if data_rx_stm32 == 0x05: platfrom_step = 3
    elif platfrom_step == 3: # 到达抓点
        if stepped_flag == 1: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 47, -math.asin(5.5 / 11.2), ACT_OPEN, 20, 50, 300, 500, 100)
        elif stepped_flag == 2: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 42, -math.asin(5.5 / 11.2), ACT_OPEN, 25, 50, 300, 500, 101)
        elif stepped_flag == 3: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 52, -math.asin(5.5 / 11.2), ACT_OPEN, 23, 50, 300, 500, 102)
    # 抓球
    elif platfrom_step == 100: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 47, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 500, 100, 5)
    elif platfrom_step == 101: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 42, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 500, 100, 5)
    elif platfrom_step == 102: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 52, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 500, 100, 5)
    # 扫码 放入框中
    elif platfrom_step == 5: step_action(1, 10, 55, POS_HOR, ACT_CLOSE, None, 50, 200, 400, 6)
    elif platfrom_step == 6: step_action(1, 22.5, 34, POS_VER, ACT_CLOSE, None, 50, 400, 500, 7)
    elif platfrom_step == 40: step_action(1, 18, 48, POS_VER, ACT_CLOSE, None, 50, 400, 400, 6)
    elif platfrom_step == 7: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 50, 700, 400, 8)
    elif platfrom_step == 8:
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 400, 300, 9)
        else: platfrom_step = 40
    elif platfrom_step == 9: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_OPEN, 20, 50, 300, 200, 10)
    elif platfrom_step == 10: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_OPEN, 20, 50, 200, 300, 11)
    elif platfrom_step == 11:
        group_index += 1
        if group_index < 8: platfrom_step = 0
        else:
            print("阶梯平台抓取结束")
            send_cmd_location_buff(0x0D, 160)
            platfrom_step = 12
    # 抓干扰球
    elif platfrom_step == 12: step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_OPEN, 20, 50, 500, 500, 13)
    elif platfrom_step == 13: step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_OPEN, 24, 50, 500, 300, 14)
    elif platfrom_step == 14: step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_CLOSE, None, 50, 500, 300, 15)
    elif platfrom_step == 15: step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_CLOSE, None, 50, 300, 300, 16)
    elif platfrom_step == 16: step_action(1, 10, 53, POS_HOR, ACT_CLOSE, None, 50, 200, 400, 17)
    # 放干扰球
    elif platfrom_step == 17:
        if stepped_flag == 1: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 47, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 400, 400, 110)
        elif stepped_flag == 2: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 42, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 400, 400, 111)
        elif stepped_flag == 3: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 53, -math.asin(5.5 / 11.2), ACT_CLOSE, None, 50, 400, 400, 112)
    elif platfrom_step == 110: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 47, -math.asin(5.5 / 11.2), ACT_OPEN, 20, 50, 500, 250, 18)
    elif platfrom_step == 111: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 42, -math.asin(5.5 / 11.2), ACT_OPEN, 25, 50, 500, 250, 18)
    elif platfrom_step == 112: step_action(0, 38.5 - L3 * math.cos(math.asin(5.5 / 11.2)), 52, -math.asin(5.5 / 11.2), ACT_OPEN, 25, 50, 500, 250, 18)
    elif platfrom_step == 18: step_action(1, 10, 55, POS_HOR, ACT_OPEN, 25, 50, 500, 300, 19)
    elif platfrom_step == 19: step_action(5, 1, 40, POS_VER, ACT_OPEN, 20, 50, 300, 600, 20)
    elif platfrom_step == 20: send_cmd_location_buff(0x0E, 160)


# 立桩
def post_get_ball():
    # 后续可以添加找绿色立桩功能
    post_k = 0.1
    global red_data, post_step, post_x_1, post_y_1, last_time_ms, ball_x, ball_y, group_index, RFID_Buff_index
    if post_step == 0: step_action(5, 1, 60, POS_HOR, ACT_OPEN, 45, 20, 500, 500, 100)  # 过渡/复位
    if post_step == 100: step_action(10, 1, 60, POS_HOR, ACT_OPEN, 30, 20, 500, 400, 1)  # 过渡
    elif post_step == 1:
        last_time_ms = pyb.millis()
        step_action(15, 1, 69, POS_HOR, ACT_OPEN, 35, 25, 400, 400, 2)  # 固定观察点
    elif post_step == 2:  # 固定观察点 解算坐标
        if delay_ms(last_time_ms, 1500):
            post_x_0 = (160 - red_data[1]) * post_k
            post_y_0 = (120 - red_data[2]) * post_k
            post_x_1 = 28.6 + post_y_0
            post_y_1 = -post_x_0
            angle = math.atan(post_y_1 / post_x_1)
            if angle < 0: angle = -angle
            ball_y = L3 * math.cos(math.asin((52 - 42) / 11.2)) * math.sin(angle)
            ball_x = L3 * math.cos(math.asin((52 - 42) / 11.2)) * math.cos(angle)
            print("post_x_1:", post_x_1, post_y_1, ball_x, ball_y)
            if post_y_1 < 0:
                post_x_1 -= ball_x
                post_y_1 += ball_y + 2
            else:
                post_x_1 -= ball_x
                post_y_1 -= ball_y
            if red_data[0] >= 1000: post_step = 4
    elif post_step == 3: step_action(post_x_1, post_y_1, 52, POS_HOR, ACT_OPEN, 30, 50, 200, 450, 4)  # 过度动作1
    elif post_step == 4: step_action(post_x_1, post_y_1, 52, -math.asin((52 - 42.3) / 11.2), ACT_OPEN, 30, 50, 450, 800, 5)  # 到达抓球点
    elif post_step == 5: step_action(post_x_1, post_y_1, 52, -math.asin((52 - 42.3) / 11.2), ACT_CLOSE, None, 50, 800, 200, 6)  # 抓球
    elif post_step == 6: step_action(post_x_1, post_y_1, 55, POS_HOR, ACT_CLOSE, None, 50, 200, 300, 61)  # 抬升
    elif post_step == 61: step_action(5, 10, 47, POS_HOR, ACT_CLOSE, None, 50, 300, 700, 7)  # 抬升
    elif post_step == 7: step_action(0, 15, 45, POS_HOR, ACT_CLOSE, None, 50, 700, 300, 8)  # 过渡动作
    elif post_step == 8: step_action(1, 22.5, 35.2, POS_VER, ACT_CLOSE, None, 40, 500, 400, 9)  # 扫码
    elif post_step == 40: step_action(1, 15, 45, POS_VER, ACT_CLOSE, None, 40, 300, 400, 8)
    elif post_step == 9: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_CLOSE, None, 40, 1000, 500, 10)  # 放球过渡
    elif post_step == 10: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 500, 300, 11)  # 放
    elif post_step == 11:
        if RFID_Buff_index == group_index + 1: step_action(*hoop_coordinates[group_index * 2 + 1], POS_VER, ACT_OPEN, 20, 40, 300, 100, 12)
        else: post_step = 40
    elif post_step == 12: step_action(*hoop_coordinates[group_index * 2], POS_VER, ACT_OPEN, 20, 40, 150, 200, 13)  # 抬升
    elif post_step == 13: step_action(1, 10, 50, POS_VER, ACT_OPEN, 20, 40, 300, 500, 14)  # 机械臂回中
    elif post_step == 14:
        group_index += 1
        if group_index < 10: post_step = 0  # 下一组
        else:
            send_cmd_location_buff(0x0F, 160)
            post_step = 15
            print("立桩任务完成")
            step_action(1, 12, 40, POS_VER, ACT_OPEN, 20, 30, 500, 350, 15)
    elif post_step == 15: send_cmd_location_buff(0x0F, 160)

# ------------- 立体仓库 --------------
find_ball_flag = [] # 1 2 3  分别对应码垛小球编号，根据索引可以判断对应码垛小球的位置
search_ball_cnt = 0 # 0 1 2  用来记录当前抓取的小球在哪一层
scan_qr_cnt = 0     # 0 1 2 对应三个二维码 用来判断小车所处位置

def warehouse_task():
    index = 0
    global warehouse_step,red_data,packet_time_ms,find_ball_flag,search_ball_cnt,ID_14_index
    global scan_qr_cnt,ID_14_index
    if len(find_ball_flag)== 1:
        index = 10
    else:
        # ID_14_index = 1
        index =ID_14_index
    #openmv_rx_stm32()
    #print("状态，收到数据,二维码：",warehouse_step,data_rx_stm32,scan_qr_cnt)
    if warehouse_step == 0: #顶层起始
        print("warehouse task start")
        step_action(0, 5, 55, -math.asin(4/11.2), ACT_OPEN, 35, 60, 500, 600, 0)
        if delay_ms(packet_time_ms,400): #隔一段时间再切换到下一步
            warehouse_step = 19
            packet_time_ms = pyb.millis()
    # ============ 第一层 ============
    if warehouse_step == 19: #观察是否有红色小球
        step_action(0, 14, 60, POS_HOR, ACT_OPEN, 35, 65, 600, 400, 19)
        if delay_ms(packet_time_ms,1000): #隔一段时间再切换到下一步
            warehouse_step = 1
            packet_time_ms = pyb.millis()
    elif warehouse_step == 1: #进去
        #time.sleep_ms(350)
        if red_data[0] >= 4000 and 1 not in find_ball_flag:
            search_ball_cnt = 0
            step_action(1, 20, 58, -math.asin(4/11.2), ACT_OPEN, 30, 15, 400, 600, 2)
        if delay_ms(packet_time_ms,1000): #这里考虑第一层没有抓到球的情况
            if 1 not in find_ball_flag :
                if scan_qr_cnt == 0:  #第一列 第一层没有球
                    warehouse_step = 20
            if red_data[0] <= 1000:
                if scan_qr_cnt == 1: #第二列 第一层没有球
                    warehouse_step = 101
                if scan_qr_cnt == 2: #第三列 第一层没有球
                    if 2 not in find_ball_flag :
                        warehouse_step = 20
                    elif 3 not in find_ball_flag :
                        warehouse_step = 30
                    else:
                        search_ball_cnt = 0
                        warehouse_step = 2
            packet_time_ms = pyb.millis()
    # ============ 第二层 ============
    elif warehouse_step == 20: #中间起始动作
        packet_time_ms = pyb.millis()
        step_action(0, 8, 48, POS_HOR, ACT_OPEN, 30, 60, 400, 600, 18)
    elif warehouse_step == 18: #中间过渡动作
        packet_time_ms = pyb.millis()
        step_action(0, 14, 48, -math.asin(2/11.2), ACT_OPEN, 35, 75, 600, 400, 21)
    elif warehouse_step == 21: #中间抓球点
        if red_data[0] >= 1000 and 2 not in find_ball_flag:
            #find_ball_flag.append(2)
            search_ball_cnt = 1
            step_action(0, 20, 45, -math.asin(2/11.2), ACT_OPEN, 30, 10, 400, 400, 2)
        if delay_ms(packet_time_ms,1000):
            if 2 not in find_ball_flag:
                if scan_qr_cnt == 0:
                    warehouse_step = 30
            if red_data[0] <= 1000:
                if scan_qr_cnt == 1:
                    if 1 not in find_ball_flag:
                        warehouse_step = 0
                    else:
                        warehouse_step = 101
                if scan_qr_cnt == 2:
                    if 3 not in find_ball_flag :
                        warehouse_step = 30
                    else:
                        search_ball_cnt = 1
                        warehouse_step = 2
                    #elif 3 not in find_ball_flag :
                        #warehouse_step = 30
            packet_time_ms = pyb.millis()
    # ============ 第三层 ============
    elif warehouse_step == 30: # 底层过渡动作，防止爪子打到小球
        packet_time_ms = pyb.millis()
        step_action(0, 6, 37, POS_HOR, ACT_OPEN, 30, 50, 600, 600, 17)
    elif warehouse_step == 17: #底层观察点
        packet_time_ms = pyb.millis()
        step_action(0, 14, 34, POS_HOR, ACT_OPEN, 30, 65, 600, 600, 31)
    elif warehouse_step == 31: #观察点3
        if red_data[0] >= 1000 and 3 not in find_ball_flag:
            search_ball_cnt = 2
            step_action(1, 20, 32, -math.asin(3/11.2), ACT_OPEN, 30, 50, 600, 600, 2)
        if delay_ms(packet_time_ms,1200):#这里考虑没有抓到球的情况
            if 3 not in find_ball_flag:
                if scan_qr_cnt == 0:
                    warehouse_step = 100
            if red_data[0] < 1000:
                if scan_qr_cnt == 1:
                    if 2 not in find_ball_flag:
                        warehouse_step = 20
                    elif 1 not in find_ball_flag:
                        warehouse_step = 0
                    else:
                        warehouse_step = 101
            packet_time_ms = pyb.millis()
    # ============ 入槽抓球 ============
    elif warehouse_step == 2: #抓球点
        if search_ball_cnt == 0: #上
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_OPEN, 30, 40, 600, 300, 3)
        elif search_ball_cnt == 1: #中
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_OPEN, 30, 40, 400, 300, 3)
        elif search_ball_cnt == 2: #下
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_OPEN, 30, 40, 400, 300, 3)
    elif warehouse_step == 3: #抓球
        if (search_ball_cnt+1) not in find_ball_flag :
            find_ball_flag.append(search_ball_cnt+1)
        if search_ball_cnt == 0: #上
            step_action(1, 25, 54, -math.asin(3/11.2), ACT_CLOSE, None, 40, 300, 100, 4)
        elif search_ball_cnt == 1: #中
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_CLOSE, None, 40, 300, 100, 4)
        elif search_ball_cnt == 2: #下
            step_action(1, 27, 30, -math.asin(5/11.2), ACT_CLOSE, None, 40, 300, 100, 4)
    # ============ 出槽放球 ============
    elif warehouse_step == 4: #入库点
        if search_ball_cnt == 0: #上
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_CLOSE, None, 40, 100, 300, 5)
        elif search_ball_cnt == 1: #中
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_CLOSE, None, 40, 100, 300, 5)
        elif search_ball_cnt == 2: #下
            step_action(1, 20, 31, POS_HOR, ACT_CLOSE, None, 40, 100, 300, 5) #-math.asin(3/11.2)
    elif warehouse_step == 5: #出来
        if search_ball_cnt == 0: #上
            step_action(1, 14, 60, -math.asin(3/11.2), ACT_CLOSE, None, 40, 400, 400, 6)
        elif search_ball_cnt == 1: #中
            step_action(1, 14, 48, -math.asin(2/11.2), ACT_CLOSE, None, 40, 400, 400, 6)
        elif search_ball_cnt == 2: #下
            step_action(1, 10, 31, POS_HOR, ACT_CLOSE, None, 40, 400, 400, 6)
    elif warehouse_step == 6: #过渡动作
        if len(find_ball_flag) < 3:
            step_action(*hoop_coordinates[index * 2], POS_VER, ACT_CLOSE, None, 40, 400, 600, 7)
        else:
            warehouse_step = 200    #这里不用延时直接跳
    elif warehouse_step ==7: #放
        step_action(*hoop_coordinates[index * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 600, 300, 8)
    elif warehouse_step ==8: #放
        step_action(*hoop_coordinates[index * 2 + 1], POS_VER, ACT_OPEN, 25, 40, 300, 100, 9)
    elif warehouse_step == 9: #过渡动作
        step_action(*hoop_coordinates[index * 2], POS_VER, ACT_OPEN, 25, 40, 100, 300, 10)
    elif warehouse_step == 10: # 回中
        packet_time_ms = pyb.millis()
        step_action(1, 12, 40, POS_VER, ACT_OPEN, 36, 30, 350, 400, 11)
    # ============ 前面两个小球抓完到这里判断下一个球看哪里 ============
    elif warehouse_step == 11: #
        #if delay_ms(packet_time_ms,500)：
        if scan_qr_cnt == 0:#第一列
            if 2 not in find_ball_flag:
                warehouse_step = 20
            elif 3 not in find_ball_flag:
                warehouse_step = 30
            if 3 in find_ball_flag and len(find_ball_flag)<3: #第三行发现球，但没找到3个
                warehouse_step = 100
        if scan_qr_cnt == 1:#第二列
            if search_ball_cnt == 2: #第三行抓到球
                if 2 not in find_ball_flag:
                    warehouse_step = 20
                elif 1 not in find_ball_flag:
                    warehouse_step = 0
            elif search_ball_cnt == 1:#第二行抓到球
                if 1 not in find_ball_flag:
                    warehouse_step = 0
                else:
                    warehouse_step = 101
            else:#到了最上层
                warehouse_step = 101
        if scan_qr_cnt == 2:#第三列
            if search_ball_cnt == 0: #第一行抓到球
                if 2 not in find_ball_flag:
                    warehouse_step = 20
                elif 3 not in find_ball_flag:
                    warehouse_step = 30
            elif search_ball_cnt == 1:#第二行抓到球
                warehouse_step = 30
        packet_time_ms = pyb.millis()
    elif warehouse_step == 200: #到这里找到三个球了 举球
        step_action(0, 5, 50, POS_HOR, ACT_CLOSE, None, 40, 500, 500, 201)
    elif warehouse_step == 201: #收到0B入库
        if len(qr_rx_buff)==1:
            scan_qr_cnt = 0
        elif len(qr_rx_buff)==2:
            scan_qr_cnt = 1
        elif len(qr_rx_buff)==3:
            scan_qr_cnt = 2
        if scan_qr_cnt== 0:#右一列抓完
            send_cmd_location_buff(0xA2,160) #右边结束发送0xA1
        elif scan_qr_cnt== 1:#中一列抓完
            send_cmd_location_buff(0xA3,160) #中间结束发送0xA3
        else:#scan_qr_cnt== 2#左一列抓完
            send_cmd_location_buff(0xA1,160) #左边结束发送0xA1
        if data_rx_stm32 == 0x0B: #收到入库指令
            warehouse_step = 90
    elif warehouse_step == 90: #起始动作
        if find_ball_flag[2] == 1:#上面
            step_action(0, 14, 60, POS_HOR, ACT_CLOSE, None, 40, 500, 600, 202)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 14, 48, -math.asin(2/11.2), ACT_CLOSE, None, 40, 500, 600, 202)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 14, 34, -math.asin(2/11.2), ACT_CLOSE, None, 40, 500, 600, 202)
    elif warehouse_step == 202: #入库点
        if find_ball_flag[2] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 400, 203)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_CLOSE, None, 40, 600, 400, 203)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 400, 203)
    elif warehouse_step == 203: #抓点
        if find_ball_flag[2] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_CLOSE, None, 40, 400, 400, 80)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_CLOSE, None, 40, 400, 400, 80)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_CLOSE, None, 40, 400, 400, 80)
    elif warehouse_step == 80: #放球
        if find_ball_flag[2] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 200, 204)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_OPEN, 30, 40, 400, 200, 204)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_OPEN, 30, 40, 400, 200, 204)
    elif warehouse_step == 204: #出来
        if find_ball_flag[2] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 81)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 400, 81)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 81)
    elif warehouse_step == 81: #出来
        if find_ball_flag[2] == 1:#上面
            step_action(0, 12, 60, POS_HOR, ACT_OPEN, 30, 40, 400, 600, 205)
        elif find_ball_flag[2] == 2:#中间
            step_action(1, 12, 48, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 205)
        elif find_ball_flag[2] == 3:#下面
            step_action(1, 12, 34, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 205)
    #---------------------中间-------------------
    elif warehouse_step == 205: #篮筐上点位
        step_action(*hoop_coordinates[10 * 2], POS_VER, ACT_OPEN, 30, 40, 600, 600, 206)
    elif warehouse_step == 206: #篮筐抓点
        step_action(*hoop_coordinates[10 * 2 + 1], POS_VER, ACT_OPEN, 30, 40, 500, 500, 207)
    elif warehouse_step == 207: #抓球
        step_action(*hoop_coordinates[10 * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 500, 300, 208)
    elif warehouse_step == 208: #篮筐上点位
        step_action(*hoop_coordinates[10 * 2], POS_VER, ACT_CLOSE, None, 40, 300, 400, 209)
    elif warehouse_step == 209: #上升
        if find_ball_flag[0] == 1:#上面
            step_action(0, 14, 60, POS_HOR, ACT_CLOSE, None, 40, 400, 600, 210)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 14, 48, -math.asin(2/11.2), ACT_CLOSE, None, 40, 400, 600, 210)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 14, 34, -math.asin(2/11.2), ACT_CLOSE, None, 40, 400, 600, 210)
    elif warehouse_step == 210: #入库点
        if find_ball_flag[0] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 600, 82)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_CLOSE, None, 40, 600, 600, 82)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 600, 82)
    elif warehouse_step == 82: #放球点
        if find_ball_flag[0] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 400, 211)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_CLOSE, None, 40, 600, 400, 211)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_CLOSE, None, 40, 600, 400, 211)
    elif warehouse_step == 211: # 放
        if find_ball_flag[0] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 200, 212)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_OPEN, 30, 40, 400, 200, 212)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_OPEN, 30, 40, 400, 200, 212)
    elif warehouse_step == 212: #出来
        if find_ball_flag[0] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 83)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 400, 83)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 83)
    elif warehouse_step == 83: #出来
        if find_ball_flag[0] == 1:#上面
            step_action(0, 12, 60, POS_HOR, ACT_OPEN, 30, 40, 400, 600, 213)
        elif find_ball_flag[0] == 2:#中间
            step_action(1, 12, 48, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 213)
        elif find_ball_flag[0] == 3:#下面
            step_action(1, 12, 34, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 213)
    #----------------------------------------
    elif warehouse_step == 213: #过渡
        step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_OPEN, 25, 40, 600, 600, 214)
    elif warehouse_step == 214: #抓球点
        step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_OPEN, 25, 40, 600, 300, 215)
    elif warehouse_step == 215: #抓球
        step_action(*hoop_coordinates[ID_14_index * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 300, 100, 216)
    elif warehouse_step == 216: #过渡
        step_action(*hoop_coordinates[ID_14_index * 2], POS_VER, ACT_CLOSE, None, 40, 100, 300, 217)
    elif warehouse_step == 217: #
        step_action(0, 7, 45, POS_HOR, ACT_CLOSE, None, 40, 300, 500, 224)
    elif warehouse_step == 224: #
        if find_ball_flag[1] == 1:#上面
            step_action(0, 14, 60, POS_HOR, ACT_CLOSE, None, 40, 500, 600, 84)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 14, 48, -math.asin(2/11.2), ACT_CLOSE, None, 40, 500, 600, 84)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 14, 34, -math.asin(2/11.2), ACT_CLOSE, None, 40, 500, 600, 84)
    elif warehouse_step == 84: #入点
        if find_ball_flag[1] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 400, 218)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_CLOSE, None, 40, 600, 400, 218)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 400, 218)
    elif warehouse_step == 218: #放点
        if find_ball_flag[1] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_CLOSE, None, 40, 400, 400, 219)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_CLOSE, None, 40, 400, 400, 219)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_CLOSE, None, 40, 400, 400, 219)
    elif warehouse_step == 219: #  放
        if find_ball_flag[1] == 1:#上面
            step_action(1, 25, 55, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 200, 220)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 27, 44, -math.asin(4/11.2), ACT_OPEN, 30, 40, 400, 200, 220)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 27, 31, -math.asin(5/11.2), ACT_OPEN, 30, 40, 400, 200, 220)
    elif warehouse_step == 220: #入点
        if find_ball_flag[1] == 1:#上面
            step_action(1, 20, 58, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 85)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 20, 45, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 400, 85)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 20, 34, -math.asin(3/11.2), ACT_OPEN, 30, 40, 400, 400, 85)
    elif warehouse_step == 85: #出来
        if find_ball_flag[1] == 1:#上面
            step_action(0, 14, 60, POS_HOR, ACT_OPEN, 30, 40, 400, 600, 223)
        elif find_ball_flag[1] == 2:#中间
            step_action(1, 14, 48, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 223)
        elif find_ball_flag[1] == 3:#下面
            step_action(1, 14, 34, -math.asin(2/11.2), ACT_OPEN, 30, 40, 400, 600, 223)
    elif warehouse_step == 223: #出来 这个阶段完成，发送0xA4
        step_action(0, 8, 45, POS_VER, ACT_OPEN, 30, 40, 600, 300, 223)
        send_cmd_location_buff(0xA4,160)
    # elif warehouse_step == 224: #出来
    #     send_cmd_location_buff(0xA4,160)
    #--------------------------------------------------
    # 右边第一例找完了没找全才会进这里
    elif warehouse_step == 100:#从这里开始第二列格子
        if len(qr_rx_buff) in [1, 2]:#第一列结束
            send_cmd_location_buff(0xA2,160) #第二列格子开始发送0xA2
            #print("收到：",data_rx_stm32)
            if data_rx_stm32 == 0x08:#小车走到中间
                print("第二列格子")
                scan_qr_cnt = 1 + scan_qr_cnt #到第二列格子时已经确定了扫到1个二维码
                #scan_qr_cnt = 1
                warehouse_step = 30 #这里已经在观察位了 需要底盘走到这里在发08
        packet_time_ms = pyb.millis()
    # 中间第一例找完了没找全才会进这里
    elif warehouse_step == 101:#从这里开始第三列格子
        if len(qr_rx_buff) in [2, 3]:#第二列结束
            send_cmd_location_buff(0xA3,160) #第三列格子开始发送0xA3
            #print("收到：",data_rx_stm32)
            if data_rx_stm32 == 0x0A:#小车走到左边
                print("第三列格子")
                scan_qr_cnt = 1 + scan_qr_cnt #到第二列格子时已经确定了扫到1个二维码
                #scan_qr_cnt = 2
                if 1 not in find_ball_flag:
                    warehouse_step = 0 #
                elif 2 not in find_ball_flag:
                    warehouse_step = 20
                elif 3 not in find_ball_flag:
                    warehouse_step = 30
        packet_time_ms = pyb.millis()

# 入库
def inbound_storage():
    global RFID_Buff,rfid_to_location,hoop_coordinates,inbound_index,idx,keys,inbound_step
    print(inbound_index,idx,inbound_step)
    if inbound_step == 0: #开始过渡动作+
        # 获取 keys 中每一个键在 RFID_Buff 中的索引 也对应了篮筐中的索引
        if RFID_Buff.index(keys[inbound_index]) is not None: idx = RFID_Buff.index(keys[inbound_index])
        else: idx = 10
        step_action(*hoop_coordinates[idx * 2], POS_VER, ACT_OPEN, 25, 40, 400, 500, 1)
    elif inbound_step == 1: #到抓球点
        step_action(*hoop_coordinates[idx * 2 + 1], POS_VER, ACT_OPEN, 25, 40, 500, 400, 2)
    elif inbound_step == 2: #抓球
        step_action(*hoop_coordinates[idx * 2 + 1], POS_VER, ACT_CLOSE, None, 40, 500, 300, 3)
    elif inbound_step == 3: #抬升
        step_action(*hoop_coordinates[idx * 2], POS_VER, ACT_CLOSE, None, 30, 300, 300, 20)
    elif inbound_step == 20: #机械臂回中
        step_action(0, 12, 40, POS_VER, ACT_CLOSE, None, 40, 300, 400, 4)
    elif inbound_step == 4: #放球中间动作
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][0], POS_HOR, ACT_CLOSE, None, 40, 400, 600, 5)
        else: step_action(*rfid_to_location[keys[inbound_index]][0], -math.asin(3/11.2), ACT_CLOSE, None, 40, 350, 600, 5)
    elif inbound_step == 5: #放球点
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][1], POS_HOR, ACT_CLOSE, None, 40, 600, 600, 6)
        else: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(3/11.2), ACT_CLOSE, None, 40, 600, 600, 6)
    elif inbound_step == 6: #放球
        if inbound_index < 6: step_action(*rfid_to_location[keys[inbound_index]][1], POS_HOR, ACT_OPEN, 25, 40, 600, 200, 7)
        else: step_action(*rfid_to_location[keys[inbound_index]][1], -math.asin(3/11.2), ACT_OPEN, 25, 40, 600, 200, 7)
    elif inbound_step == 7: #退回
        if inbound_index < 6:#上面两行
            step_action(*rfid_to_location[keys[inbound_index]][0], POS_HOR, ACT_CLOSE, None, 40, 200, 600, 9)
        else:#最下面一行
            step_action(*rfid_to_location[keys[inbound_index]][0], -math.asin(3/11.2), ACT_CLOSE, None, 30, 200, 600, 9)
    elif inbound_step == 8: #机械臂回中
        step_action(0, 12, 40, POS_VER, ACT_CLOSE, None, 30, 600, 600, 10)
    elif inbound_step == 9: #
        inbound_index = 1 + inbound_index
        if inbound_index < 9: inbound_step = 0
        else: inbound_step = 8
    elif inbound_step == 10: #
        send_cmd_location_buff(0xA5,160)


def openmv_rx_stm32():
    global task_flag,data_rx_stm32,qr_rx_buff
    global RFID_Buff,ID_14_index,RFID_Buff_index
    re_list_stm32 = []
    if uart_stn32.any():
        data = uart_stn32.read()
        #print("从stm32收到的数据：",data)
        if data:
            # print("data:",data)
            re_list_stm32.extend(data)  # 将接收到的数据添加到列表中
            if len(re_list_stm32) >= 3:
                if re_list_stm32[0] == 0xAB and re_list_stm32[2] == 0xEF:
                    re_cmd = re_list_stm32[1]  # 提取命令字节
                    #print("re_cmd:",re_cmd)
                    if re_cmd == 1:
                        task_flag = 1
                    elif re_cmd == 2:
                        task_flag = 2
                    elif re_cmd == 3 :
                        task_flag = 3
                    elif re_cmd == 6 :
                        task_flag = 4
                    elif re_cmd == 7 :
                        task_flag = 5
                    elif re_cmd == 0x0C :
                        task_flag = 6
                    data_rx_stm32 = re_cmd
                    #print(task_flag)
                    return re_cmd
                #读卡器
                elif re_list_stm32[0] == 0x55 and re_list_stm32[2] == 0x66:
                    if re_list_stm32[1] not in RFID_Buff:
                        send_cmd_location_buff(re_list_stm32[1],160)
                        if re_list_stm32[1] == 0x14:
                            ID_14_index = RFID_Buff_index
                        RFID_Buff.append((re_list_stm32[1]))
                        RFID_Buff_index = RFID_Buff_index+1
                    print("RFID:",re_list_stm32[1])
                    print(RFID_Buff)
                    return re_list_stm32[1]
                #二维码
                elif re_list_stm32[0] == 0x77 and re_list_stm32[2] == 0x88:
                    if re_list_stm32[1] not in qr_rx_buff and re_list_stm32[1] in [0x31,0x32,0x33]:
                        #send_cmd_location_buff(re_list_stm32[1],160)
                        qr_rx_buff.append(re_list_stm32[1]) #例如：0x31-0x20==0x11
                    print("qr_rx_buff:",len(qr_rx_buff))
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
    #print("发送：",cmd,location)


def search_red():
    global task_flag,color_blob_1
    area = 0
    if task_flag == 5:
        my_threshold = blue_threshold_warehouse
    else :
        my_threshold = blue_threshold
    #if task_flag == 3:
        #my_roi = stepplatfrom_roi
    if task_flag == 1:
        my_roi = DISKROI
    elif task_flag == 3:
        my_roi = stepplatfrom_roi
    else:
        my_roi = ROI
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
            lcd.display(img)
            # print("area=",area)
            return area,blob.cx(),blob.cy()
    else :
        openmv_rx_stm32()
        lcd.display(img)
        #print("area=",area)
        return 0,0,0

def search_white():
    global is_send_data,task_flag
    openmv_rx_stm32()
    img = sensor.snapshot().lens_corr(1.2)  # 每次拍新图
    img.draw_rectangle(ROI)
    #pixels_threshold 最低像素点  area_threshold  最低面积 长*宽 merge=True 如果多个相邻的 blobs 符合条件，会把它们合并成一个大的 blob
    blobs = img.find_blobs([white_threshold],roi = ROI , pixels_threshold=500, area_threshold=1000, merge=True)
    if blobs :
        for blob in blobs:
            x = blob[0]
            y = blob[1] #
            width = blob[2]
            height = blob[3]
            area = float(blob.area())
            print("area:",area)
            if area>= 8000 : #and is_send_data == 1
                send_cmd_location_buff(0x0B,160)
                time.sleep_ms(2)
                send_cmd_location_buff(0x0B,160)
                step_action(1, 10, 45, POS_VER, ACT_OPEN, 25, 40, 200, 300, 1)
            else :
                send_cmd_location_buff(0x20,160)
                time.sleep_ms(2)
                send_cmd_location_buff(0x20,160)
            img.draw_string(blob.cx(),blob.cy(), "white", color = (0xFF, 0x00, 0x00))
            img.draw_rectangle([x, y, width, height])
            img.draw_cross(blob.cx(), blob.cy())
            lcd.display(img)
            return area,x,y
    else :
        send_cmd_location_buff(0x20,160)
        #send_data_packet([0x20])
        lcd.display(img)
        # video.record(img, clock.fps()) # 录制视频
        return 0,0,0

while True:
    clock.tick()
    #search_red()
    #search_white()
    #---------------------------------------------------------------
    if flag == 1 :#7500 17160 4000
        enter = 1
        send_cmd_location_buff(0x51,160)
        #angle_180[0],angle_180[1],angle_180[2]=arm_control(0,34-L3*math.cos(math.asin((47-41.5)/11.2)),45)  #0,15,35
        angle_180[0],angle_180[1],angle_180[2]=arm_control(0,38.5 - L3*math.cos(math.asin(5.5/11.2)),52)  #0,15,35
        angle_180[0],angle_180[1],angle_180[2]=arm_control(14,29,30)
        angle_180[0],angle_180[1],angle_180[2]=arm_control(0,15,35)
        angle_180[0],angle_180[1],angle_180[2]=arm_control(1,14,45)
        set_gripper_position(-math.asin(3/11.2))
        set_gripper_position(POS_VER)
        # set_gripper_position(POS_HOR)

        set_gripper_action(ACT_OPEN,35)
        #set_gripper_action(ACT_CLOSE,None)
        set_camera_position(50)
        # set_camera_position(POS_VER)
        #set_camera_position()
        SetMultiServoAngle(600,angle_180)
        flag = 0
    #---------------------------------------------------------------
    stm32_cmd = openmv_rx_stm32() #接收CMD

    if task_flag == 1:
        red_data = search_red()
        get_ball_disk()
    elif task_flag == 2:
        white_data = search_white()
        print("area:",white_data[0])
    elif task_flag == 3:
        if flag == 0 :
            group_index = 6
            flag = 2
        red_data = search_red()
        stepped_platfrom()

    elif task_flag == 4:
        if flag == 2 :
            group_index = 8
            flag = 3
        red_data = search_red()
        post_get_ball()
    elif task_flag == 5:
        #print(warehouse_step,find_ball_flag)
        red_data = search_red()
        #send_cmd_location_buff(warehouse_step,160) #第二列格子开始发送0xA2
        warehouse_task()
    elif task_flag == 6:
        if enter == 1:
            send_cmd_location_buff(0xCC,160)
            #利用二维码补充立体仓库货架位置  现在位置都有了，可以写搬运动作了
            qr_to_loocation()
            print("ok")
            inbound_index = 0
            enter = 4
        inbound_storage()
        #print(keys)
    else:
        if data_rx_stm32  == 0x0C:
            send_cmd_location_buff(0x0C,160)
    #print(qr_rx_buff , RFID_Buff)
    # time.sleep_ms(2)

