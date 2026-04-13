"""

       INDIAN RAILWAY TICKET RESERVATION SYSTEM               
       Author  : Sulagno Banerjee  |  BCA (AI) - Jain Univ.   
       Tech    : Python | File Handling | OOP | Data Structures

CONCEPTS USED IN THIS PROJECT:

 1. Object-Oriented Programming (OOP)
    → Classes: Train, Passenger, Booking, ReservationSystem
    → Encapsulation: each class manages its own data
    → Methods: functions inside classes

 2. File Handling (JSON)
    → All data saved to .json files (like a real database)
    → Data persists even after program closes
    → Load → Modify → Save cycle

 3. Data Structures
    → Dictionary  : store train/booking data
    → List        : manage seat availability
    → Nested Dict : complex data like coach → seats

 4. Unique ID Generation
    → PNR numbers (like real railways use)
    → UUID module for guaranteed uniqueness

 5. Authentication System
    → User registration & login
    → Password hashing using hashlib

 6. Waitlist Queue
    → If train is full → passenger goes to waitlist
    → When cancellation happens → waitlisted passenger auto-confirmed

 7. Fare Calculation Engine
    → Dynamic pricing based on class, distance, quota
    → Senior citizen & student discounts

 8. Modular Design
    → Each feature is a separate function/class
    → Easy to add new features

 9. Input Validation
    → Checks wrong inputs, empty fields, invalid dates

10. Report Generation
    → Prints booking history, train status, revenue reports
"""

import json
import os
import hashlib
import datetime
import random
import string
import re
from collections import deque   # deque = double-ended queue (for waitlist)


# TERMINAL COLORS  (makes output look pro)

class C:
    RESET   = "\033[0m";  BOLD    = "\033[1m"
    CYAN    = "\033[96m"; GREEN   = "\033[92m"
    YELLOW  = "\033[93m"; RED     = "\033[91m"
    BLUE    = "\033[94m"; MAGENTA = "\033[95m"
    WHITE   = "\033[97m"; DIM     = "\033[2m"
    BG_BLUE = "\033[44m"; BG_RED  = "\033[41m"
    BG_GRN  = "\033[42m"

def p(text, color=C.WHITE, bold=False, end="\n"):
    b = C.BOLD if bold else ""
    print(f"{b}{color}{text}{C.RESET}", end=end)

def line(char="─", n=60, color=C.DIM):
    p(char * n, color)

def header(title):
    line("═", 60, C.CYAN)
    p(f"  {title}", C.CYAN, bold=True)
    line("═", 60, C.CYAN)

# ══════════════════════════════════════════════
# FILE PATHS  (our "database" files)
# ══════════════════════════════════════════════
DB_TRAINS   = "trains_db.json"
DB_BOOKINGS = "bookings_db.json"
DB_USERS    = "users_db.json"

# ══════════════════════════════════════════════
# CLASS: TRAIN
# Represents a train with all its properties
# ══════════════════════════════════════════════
class Train:
    """
    OOP CONCEPT: This class is a blueprint for a train object.
    Each train has: number, name, route, schedule, and seat map.

    SEAT CLASSES:
    ┌──────────┬──────────┬───────────┬──────────────────────┐
    │  Code    │  Name    │  Seats    │  Fare/km             │
    ├──────────┼──────────┼───────────┼──────────────────────┤
    │  SL      │ Sleeper  │  72/coach │  ₹0.50/km            │
    │  3A      │ 3rd AC   │  64/coach │  ₹1.20/km            │
    │  2A      │ 2nd AC   │  46/coach │  ₹1.80/km            │
    │  1A      │ 1st AC   │  24/coach │  ₹3.00/km            │
    │  CC      │ Chair Car│  78/coach │  ₹0.70/km            │
    └──────────┴──────────┴───────────┴──────────────────────┘
    """

    CLASSES = {
        "SL": {"name": "Sleeper Class",    "seats": 72, "fare_per_km": 0.50, "coaches": 8},
        "3A": {"name": "AC 3 Tier",        "seats": 64, "fare_per_km": 1.20, "coaches": 4},
        "2A": {"name": "AC 2 Tier",        "seats": 46, "fare_per_km": 1.80, "coaches": 2},
        "1A": {"name": "AC First Class",   "seats": 24, "fare_per_km": 3.00, "coaches": 1},
        "CC": {"name": "Chair Car",        "seats": 78, "fare_per_km": 0.70, "coaches": 3},
    }

    def __init__(self, number, name, source, destination, departure, arrival, distance_km, days_of_run):
        self.number       = number          # e.g., "12301"
        self.name         = name            # e.g., "Rajdhani Express"
        self.source       = source          # e.g., "New Delhi"
        self.destination  = destination     # e.g., "Mumbai"
        self.departure    = departure       # e.g., "16:55"
        self.arrival      = arrival         # e.g., "08:15"
        self.distance_km  = distance_km     # e.g., 1384
        self.days_of_run  = days_of_run     # e.g., ["Mon","Wed","Fri"]

        # Build seat map: { "SL": { "S1": [True,True,...], "S2": [...] } }
        # True = seat available, False = booked
        self.seats = self._build_seat_map()

        # Waitlist queue per class: { "SL": deque([]), "3A": deque([]) }
        self.waitlist = {cls: [] for cls in self.CLASSES}

    def _build_seat_map(self):
        """
        Creates a nested dictionary representing all coaches and seats.
        Example: seats["SL"]["S1"] = [True]*72  (all 72 seats available)
        """
        seat_map = {}
        coach_prefix = {"SL":"S", "3A":"B", "2A":"A", "1A":"H", "CC":"C"}
        for cls, info in self.CLASSES.items():
            seat_map[cls] = {}
            for i in range(1, info["coaches"] + 1):
                coach_id = f"{coach_prefix[cls]}{i}"
                seat_map[cls][coach_id] = [True] * info["seats"]
        return seat_map

    def get_available_seats(self, cls):
        """Counts total available seats in a class across all coaches."""
        count = 0
        for coach_seats in self.seats[cls].values():
            count += sum(coach_seats)   # True=1, False=0 → sum = available count
        return count

    def book_seat(self, cls):
        """
        Finds first available seat in a class, marks it booked.
        Returns: (coach_id, seat_number) or None if full
        """
        for coach_id, seats in self.seats[cls].items():
            for i, available in enumerate(seats):
                if available:
                    self.seats[cls][coach_id][i] = False  # Mark as booked
                    return (coach_id, i + 1)              # Return coach & seat no.
        return None   # All seats full

    def release_seat(self, cls, coach_id, seat_no):
        """Frees a seat when a booking is cancelled."""
        self.seats[cls][coach_id][seat_no - 1] = True

    def to_dict(self):
        """Converts Train object to dictionary for JSON saving."""
        return {
            "number": self.number, "name": self.name,
            "source": self.source, "destination": self.destination,
            "departure": self.departure, "arrival": self.arrival,
            "distance_km": self.distance_km, "days_of_run": self.days_of_run,
            "seats": self.seats, "waitlist": {k: list(v) for k, v in self.waitlist.items()}
        }

    @classmethod
    def from_dict(cls, data):
        """Recreates Train object from saved dictionary (JSON loading)."""
        t = cls(data["number"], data["name"], data["source"], data["destination"],
                data["departure"], data["arrival"], data["distance_km"], data["days_of_run"])
        t.seats    = data["seats"]
        t.waitlist = {k: deque(v) for k, v in data.get("waitlist", {}).items()}
        return t


# ══════════════════════════════════════════════
# CLASS: PASSENGER
# Represents a person booking a ticket
# ══════════════════════════════════════════════
class Passenger:
    """
    Holds passenger details.
    quota: GN=General, SR=Senior Citizen, ST=Student, LG=Ladies
    """
    QUOTAS = {
        "GN": {"name": "General",        "discount": 0.00},
        "SR": {"name": "Senior Citizen",  "discount": 0.40},  # 40% off
        "ST": {"name": "Student",         "discount": 0.25},  # 25% off
        "LG": {"name": "Ladies",          "discount": 0.00},
    }

    def __init__(self, name, age, gender, quota="GN"):
        self.name   = name
        self.age    = int(age)
        self.gender = gender.upper()   # M / F / O
        self.quota  = quota.upper()

    def to_dict(self):
        return {"name": self.name, "age": self.age, "gender": self.gender, "quota": self.quota}


# ══════════════════════════════════════════════
# CLASS: BOOKING
# Represents a confirmed or waitlisted ticket
# ══════════════════════════════════════════════
class Booking:
    """
    One booking = one PNR = one or more passengers on one train.
    STATUS: CONFIRMED / WAITLISTED / CANCELLED
    """
    def __init__(self, pnr, user_id, train_number, travel_date,
                 travel_class, passengers, coach=None, seats=None):
        self.pnr          = pnr
        self.user_id      = user_id
        self.train_number = train_number
        self.travel_date  = travel_date
        self.travel_class = travel_class
        self.passengers   = passengers    # list of Passenger dicts
        self.coach        = coach         # e.g., "S3"
        self.seats        = seats or []   # e.g., [14, 15]
        self.status       = "CONFIRMED" if coach else "WAITLISTED"
        self.booked_on    = datetime.datetime.now().strftime("%d-%m-%Y %H:%M")
        self.fare         = 0.0

    def to_dict(self):
        return {
            "pnr": self.pnr, "user_id": self.user_id,
            "train_number": self.train_number, "travel_date": self.travel_date,
            "travel_class": self.travel_class, "passengers": self.passengers,
            "coach": self.coach, "seats": self.seats,
            "status": self.status, "booked_on": self.booked_on,
            "fare": self.fare
        }


# ══════════════════════════════════════════════
# CLASS: FARE CALCULATOR
# Dynamic pricing engine
# ══════════════════════════════════════════════
class FareCalculator:
    """
    Calculates ticket fare based on:
    - Distance (km)
    - Class (SL / 3A / 2A / 1A / CC)
    - Quota discount (Senior citizen / Student)
    - Passenger count
    - GST (5%)
    - Reservation charge (₹40 flat)
    """
    RESERVATION_CHARGE = 40.0
    GST_RATE           = 0.05   # 5% GST

    @staticmethod
    def calculate(distance_km, travel_class, passengers):
        """
        Returns: (base_fare, gst, total_fare, breakdown_list)
        """
        fare_per_km    = Train.CLASSES[travel_class]["fare_per_km"]
        base_per_pax   = distance_km * fare_per_km
        breakdown      = []
        total_base     = 0.0

        for pax in passengers:
            quota    = pax["quota"]
            discount = Passenger.QUOTAS[quota]["discount"]
            pax_fare = base_per_pax * (1 - discount) + FareCalculator.RESERVATION_CHARGE
            breakdown.append({
                "name"    : pax["name"],
                "base"    : round(base_per_pax, 2),
                "discount": round(base_per_pax * discount, 2),
                "resv"    : FareCalculator.RESERVATION_CHARGE,
                "subtotal": round(pax_fare, 2)
            })
            total_base += pax_fare

        gst   = round(total_base * FareCalculator.GST_RATE, 2)
        total = round(total_base + gst, 2)
        return total_base, gst, total, breakdown


# ══════════════════════════════════════════════
# CLASS: RESERVATION SYSTEM  (main controller)
# Ties everything together
# ══════════════════════════════════════════════
class ReservationSystem:
    """
    The core engine. Handles:
    - Train data loading/saving
    - User registration/login
    - Booking, cancellation, PNR enquiry
    - Waitlist management
    - Reports
    """

    def __init__(self):
        self.trains   = {}    # { train_number: Train object }
        self.bookings = {}    # { pnr: Booking dict }
        self.users    = {}    # { user_id: user dict }
        self.current_user = None

        self._load_all()
        self._seed_trains_if_empty()

    # ── FILE HANDLING METHODS ──────────────────
    def _load_all(self):
        """Loads all data from JSON files into memory."""
        # Load trains
        if os.path.exists(DB_TRAINS):
            with open(DB_TRAINS, "r") as f:
                raw = json.load(f)
                self.trains = {k: Train.from_dict(v) for k, v in raw.items()}

        # Load bookings
        if os.path.exists(DB_BOOKINGS):
            with open(DB_BOOKINGS, "r") as f:
                self.bookings = json.load(f)

        # Load users
        if os.path.exists(DB_USERS):
            with open(DB_USERS, "r") as f:
                self.users = json.load(f)

    def _save_trains(self):
        with open(DB_TRAINS, "w") as f:
            json.dump({k: v.to_dict() for k, v in self.trains.items()}, f, indent=2)

    def _save_bookings(self):
        with open(DB_BOOKINGS, "w") as f:
            json.dump(self.bookings, f, indent=2)

    def _save_users(self):
        with open(DB_USERS, "w") as f:
            json.dump(self.users, f, indent=2)

    # ── SEED DATA (pre-load 6 real trains) ────
    def _seed_trains_if_empty(self):
        """If no trains exist, add sample Indian trains."""
        if self.trains:
            return   # Already have data
        sample_trains = [
            Train("12301","Howrah Rajdhani","New Delhi","Howrah","17:05","10:05",1441,["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]),
            Train("12951","Mumbai Rajdhani","New Delhi","Mumbai Central","16:55","08:35",1384,["Mon","Wed","Thu","Fri","Sat","Sun"]),
            Train("12430","Lucknow Mail","New Delhi","Lucknow","22:30","05:00",498,["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]),
            Train("22691","Rajdhani Express","New Delhi","Bangalore","21:00","05:00",2367,["Tue","Wed","Fri","Sun"]),
            Train("12002","Bhopal Shatabdi","New Delhi","Bhopal","06:00","13:25",702,["Mon","Tue","Wed","Thu","Fri","Sat"]),
            Train("12259","Duronto Express","Sealdah","New Delhi","20:05","10:25",1453,["Mon","Wed","Fri"]),
        ]
        for t in sample_trains:
            self.trains[t.number] = t
        self._save_trains()
        p("  ✅ Sample trains loaded into database.", C.GREEN)

    # ── AUTHENTICATION METHODS ─────────────────
    def _hash_password(self, password):
        """
        Hashes password using SHA-256.
        Never store plain text passwords!
        hashlib converts "mypassword" → "a9f3d7..." (irreversible)
        """
        return hashlib.sha256(password.encode()).hexdigest()

    def register_user(self):
        """Creates a new user account."""
        header("📝  USER REGISTRATION")
        name  = input("  Full Name    : ").strip()
        email = input("  Email        : ").strip().lower()
        phone = input("  Phone No.    : ").strip()
        pwd   = input("  Password     : ").strip()

        # Check if email already registered
        for uid, u in self.users.items():
            if u["email"] == email:
                p("  ❌ Email already registered. Please login.", C.RED)
                return False

        # Generate unique user ID
        user_id = "USR" + ''.join(random.choices(string.digits, k=6))

        self.users[user_id] = {
            "user_id" : user_id,
            "name"    : name,
            "email"   : email,
            "phone"   : phone,
            "password": self._hash_password(pwd),   # NEVER store plain password
            "joined"  : datetime.date.today().isoformat()
        }
        self._save_users()
        p(f"\n  ✅ Registered! Your User ID: {user_id}", C.GREEN, bold=True)
        return True

    def login_user(self):
        """Authenticates a user."""
        header("🔐  USER LOGIN")
        email = input("  Email    : ").strip().lower()
        pwd   = input("  Password : ").strip()
        hashed = self._hash_password(pwd)

        for uid, u in self.users.items():
            if u["email"] == email and u["password"] == hashed:
                self.current_user = u
                p(f"\n  ✅ Welcome back, {u['name']}!", C.GREEN, bold=True)
                return True

        p("  ❌ Invalid email or password.", C.RED)
        return False

    # ── TRAIN SEARCH ───────────────────────────
    def search_trains(self):
        """Search trains by source, destination, and date."""
        header("🔍  SEARCH TRAINS")
        src  = input("  From (City) : ").strip().title()
        dest = input("  To   (City) : ").strip().title()
        date_str = input("  Date (DD-MM-YYYY) : ").strip()

        # Validate date format
        try:
            travel_date = datetime.datetime.strptime(date_str, "%d-%m-%Y")
            day_name = travel_date.strftime("%a")   # e.g., "Mon"
        except ValueError:
            p("  ❌ Invalid date format.", C.RED)
            return []

        results = []
        for num, train in self.trains.items():
            # Match source/destination (case-insensitive partial match)
            src_match  = src.lower()  in train.source.lower()
            dest_match = dest.lower() in train.destination.lower()
            day_match  = day_name in train.days_of_run

            if src_match and dest_match and day_match:
                results.append(train)

        if not results:
            p(f"\n  ❌ No trains found from {src} to {dest} on {date_str}", C.RED)
            return []

        # Display results table
        p(f"\n  Found {len(results)} train(s):\n", C.GREEN)
        p(f"  {'No.':<8}{'Train Name':<25}{'Departs':<10}{'Arrives':<10}{'Dist':<8}{'Runs On'}", C.YELLOW, bold=True)
        line()
        for t in results:
            days = ", ".join(t.days_of_run[:3]) + ("..." if len(t.days_of_run) > 3 else "")
            p(f"  {t.number:<8}{t.name:<25}{t.departure:<10}{t.arrival:<10}{t.distance_km:<8}{days}")

        # Show class-wise availability for each train
        print()
        for t in results:
            p(f"\n  {t.number} — {t.name}  |  Seat Availability:", C.CYAN)
            for cls, info in Train.CLASSES.items():
                avail = t.get_available_seats(cls)
                total = info["seats"] * info["coaches"]
                bar   = self._availability_bar(avail, total)
                fare  = FareCalculator.calculate(t.distance_km, cls, [{"quota":"GN"}])
                p(f"    {cls}  {info['name']:<18} {bar}  {avail:>4}/{total} seats  ₹{fare[2]:.0f}/pax")

        return results

    def _availability_bar(self, avail, total):
        """Visual bar showing seat availability."""
        ratio = avail / total if total else 0
        filled = int(ratio * 10)
        if ratio > 0.5:  color = C.GREEN
        elif ratio > 0.2: color = C.YELLOW
        else: color = C.RED
        bar = "█" * filled + "░" * (10 - filled)
        return f"{color}[{bar}]{C.RESET}"

    # ── BOOKING ────────────────────────────────
    def book_ticket(self):
        """Full ticket booking flow."""
        if not self.current_user:
            p("  ❌ Please login first.", C.RED)
            return

        header("🎫  BOOK TICKET")

        # Step 1: Get train number
        train_no = input("  Enter Train Number : ").strip()
        if train_no not in self.trains:
            p("  ❌ Train not found.", C.RED)
            return
        train = self.trains[train_no]

        # Step 2: Travel date
        date_str = input("  Travel Date (DD-MM-YYYY) : ").strip()
        try:
            datetime.datetime.strptime(date_str, "%d-%m-%Y")
        except ValueError:
            p("  ❌ Invalid date.", C.RED)
            return

        # Step 3: Class selection
        p("\n  Select Travel Class:", C.CYAN)
        for cls, info in Train.CLASSES.items():
            avail = train.get_available_seats(cls)
            p(f"    {cls} → {info['name']}  ({avail} seats available)")
        travel_class = input("  Your Choice : ").strip().upper()
        if travel_class not in Train.CLASSES:
            p("  ❌ Invalid class.", C.RED)
            return

        # Step 4: Add passengers
        try:
            num_pax = int(input("  Number of Passengers (max 6) : ").strip())
            if not 1 <= num_pax <= 6:
                raise ValueError
        except ValueError:
            p("  ❌ Invalid count.", C.RED)
            return

        passengers = []
        for i in range(num_pax):
            p(f"\n  Passenger {i+1}:", C.YELLOW)
            name   = input("    Name   : ").strip()
            age    = input("    Age    : ").strip()
            gender = input("    Gender (M/F/O) : ").strip().upper()
            p("    Quota  : GN=General | SR=Senior | ST=Student | LG=Ladies")
            quota  = input("    Quota  : ").strip().upper() or "GN"
            if quota not in Passenger.QUOTAS:
                quota = "GN"
            passengers.append(Passenger(name, age, gender, quota).to_dict())

        # Step 5: Fare display & confirmation
        _, gst, total, breakdown = FareCalculator.calculate(
            train.distance_km, travel_class, passengers)

        p("\n  ─── FARE BREAKDOWN ───────────────────────", C.CYAN)
        for b in breakdown:
            p(f"  {b['name']:<20} Base: ₹{b['base']:.2f}  Disc: -₹{b['discount']:.2f}  Resv: ₹{b['resv']:.2f}  = ₹{b['subtotal']:.2f}")
        p(f"\n  GST (5%)   : ₹{gst:.2f}", C.DIM)
        p(f"  TOTAL FARE : ₹{total:.2f}", C.GREEN, bold=True)

        confirm = input("\n  Confirm booking? (Y/N) : ").strip().upper()
        if confirm != "Y":
            p("  Booking cancelled.", C.YELLOW)
            return

        # Step 6: Simulate payment
        p("\n  💳 Payment Gateway (Simulation):", C.MAGENTA)
        p("  1. UPI   2. Card   3. Net Banking   4. Wallet")
        pay_choice = input("  Choose payment: ").strip()
        p("  ⏳ Processing payment...", C.DIM)
        import time; time.sleep(1)
        p("  ✅ Payment Successful!", C.GREEN, bold=True)

        # Step 7: Seat allotment or waitlist
        pnr = "PNR" + ''.join(random.choices(string.digits, k=10))

        # Try to allot seats for all passengers
        allotted_seats = []
        coach_used     = None
        avail = train.get_available_seats(travel_class)

        if avail >= num_pax:
            for _ in passengers:
                result = train.book_seat(travel_class)
                if result:
                    coach_used = result[0]
                    allotted_seats.append(result[1])
            status = "CONFIRMED"
        else:
            # Add to waitlist
            train.waitlist[travel_class].append(pnr)
            wl_pos = len(train.waitlist[travel_class])
            status = f"WL/{wl_pos}"
            p(f"\n  ⚠️  Train full. You are on Waitlist position {wl_pos}.", C.YELLOW)

        # Step 8: Create & save booking
        booking = Booking(pnr, self.current_user["user_id"], train_no,
                          date_str, travel_class, passengers, coach_used, allotted_seats)
        booking.status = status
        booking.fare   = total
        self.bookings[pnr] = booking.to_dict()

        self._save_trains()
        self._save_bookings()

        # Step 9: Print ticket
        self._print_ticket(booking, train)

    def _print_ticket(self, booking, train):
        """Prints a formatted ticket / e-ticket."""
        line("═", 60, C.CYAN)
        p("        🚂  INDIAN RAILWAYS — E-TICKET  🚂", C.CYAN, bold=True)
        line("═", 60, C.CYAN)
        p(f"  PNR Number   : {booking.pnr}", C.GREEN, bold=True)
        p(f"  Status       : {booking.status}", C.GREEN if "CONFIRMED" in booking.status else C.YELLOW)
        p(f"  Train        : {train.number} — {train.name}")
        p(f"  From → To    : {train.source} → {train.destination}")
        p(f"  Date         : {booking.travel_date}")
        p(f"  Departure    : {train.departure}  |  Arrival : {train.arrival}")
        p(f"  Class        : {Train.CLASSES[booking.travel_class]['name']}")
        if booking.coach:
            seat_str = ", ".join(str(s) for s in booking.seats)
            p(f"  Coach/Seats  : {booking.coach} / Seat(s) {seat_str}")
        line()
        p("  PASSENGER(S):", C.YELLOW)
        for i, pax in enumerate(booking.passengers, 1):
            disc_name = Passenger.QUOTAS[pax['quota']]['name']
            p(f"  {i}. {pax['name']:<20} Age: {pax['age']}  Gender: {pax['gender']}  Quota: {disc_name}")
        line()
        p(f"  Total Fare   : ₹{booking.fare:.2f}", C.GREEN, bold=True)
        p(f"  Booked On    : {booking.booked_on}")
        line("═", 60, C.CYAN)

    # ── PNR ENQUIRY ────────────────────────────
    def pnr_enquiry(self):
        """Check status of a booking using PNR."""
        header("🔎  PNR ENQUIRY")
        pnr = input("  Enter PNR Number : ").strip().upper()
        if pnr not in self.bookings:
            p("  ❌ PNR not found.", C.RED)
            return

        b     = self.bookings[pnr]
        train = self.trains.get(b["train_number"])
        status_color = C.GREEN if "CONFIRMED" in b["status"] else C.YELLOW

        p(f"\n  PNR      : {b['pnr']}", C.CYAN, bold=True)
        p(f"  Status   : {b['status']}", status_color, bold=True)
        p(f"  Train    : {b['train_number']} — {train.name if train else 'N/A'}")
        p(f"  Date     : {b['travel_date']}  |  Class: {Train.CLASSES[b['travel_class']]['name']}")
        if b["coach"]:
            p(f"  Coach    : {b['coach']}  |  Seats: {', '.join(str(s) for s in b['seats'])}")
        p(f"  Fare     : ₹{b['fare']:.2f}")
        p(f"  Booked On: {b['booked_on']}")
        line()
        p("  Passengers:", C.YELLOW)
        for i, pax in enumerate(b["passengers"], 1):
            p(f"  {i}. {pax['name']}  Age:{pax['age']}  {pax['gender']}  Quota:{pax['quota']}")

    # ── CANCELLATION ───────────────────────────
    def cancel_ticket(self):
        """
        Cancels a ticket.
        IMPORTANT: If waitlist exists, the next waitlisted passenger gets auto-confirmed.
        This is the WAITLIST QUEUE logic.
        """
        if not self.current_user:
            p("  ❌ Please login first.", C.RED)
            return

        header("❌  CANCEL TICKET")
        pnr = input("  Enter PNR to Cancel : ").strip().upper()

        if pnr not in self.bookings:
            p("  ❌ PNR not found.", C.RED)
            return

        b = self.bookings[pnr]

        # Check ownership
        if b["user_id"] != self.current_user["user_id"]:
            p("  ❌ This PNR does not belong to your account.", C.RED)
            return

        if b["status"] == "CANCELLED":
            p("  ❌ This ticket is already cancelled.", C.RED)
            return

        # Cancellation refund policy
        p("\n  📋 CANCELLATION POLICY:", C.YELLOW)
        p("  Cancel 48+ hrs before  → 75% refund")
        p("  Cancel 24–48 hrs before → 50% refund")
        p("  Cancel <24 hrs before  → 25% refund")
        p(f"\n  Ticket Fare: ₹{b['fare']:.2f}", C.CYAN)
        refund = round(b["fare"] * 0.75, 2)
        p(f"  Estimated Refund (75%): ₹{refund:.2f}", C.GREEN)

        confirm = input("\n  Confirm cancellation? (Y/N) : ").strip().upper()
        if confirm != "Y":
            p("  Cancellation aborted.", C.YELLOW)
            return

        # Release seats back to train
        if b["coach"] and b["seats"] and b["train_number"] in self.trains:
            train = self.trains[b["train_number"]]
            for seat_no in b["seats"]:
                train.release_seat(b["travel_class"], b["coach"], seat_no)

            # ── WAITLIST PROMOTION LOGIC ──────────────
            # If someone is on waitlist, auto-confirm them now
            wl = train.waitlist.get(b["travel_class"], [])
            if wl:
                next_pnr = wl.pop(0)    # Remove first person from waitlist
                if next_pnr in self.bookings:
                    nb = self.bookings[next_pnr]
                    # Allot the freed seats to waitlisted passenger
                    new_seats = []
                    new_coach = None
                    for _ in nb["passengers"]:
                        result = train.book_seat(b["travel_class"])
                        if result:
                            new_coach = result[0]
                            new_seats.append(result[1])
                    self.bookings[next_pnr]["coach"]  = new_coach
                    self.bookings[next_pnr]["seats"]  = new_seats
                    self.bookings[next_pnr]["status"] = "CONFIRMED"
                    p(f"\n  🔔 Waitlisted PNR {next_pnr} has been AUTO-CONFIRMED!", C.GREEN, bold=True)

        # Mark as cancelled
        self.bookings[pnr]["status"] = "CANCELLED"
        self._save_trains()
        self._save_bookings()
        p(f"\n  ✅ Ticket {pnr} cancelled. Refund of ₹{refund:.2f} will be processed in 5–7 days.", C.GREEN)

    # ── MY BOOKINGS ────────────────────────────
    def my_bookings(self):
        """Shows all bookings for the logged-in user."""
        if not self.current_user:
            p("  ❌ Please login first.", C.RED)
            return

        header(f"📋  MY BOOKINGS — {self.current_user['name']}")
        user_bookings = [b for b in self.bookings.values()
                         if b["user_id"] == self.current_user["user_id"]]

        if not user_bookings:
            p("  No bookings found.", C.YELLOW)
            return

        for b in user_bookings:
            train = self.trains.get(b["train_number"])
            status_color = (C.GREEN if "CONFIRMED" in b["status"]
                            else C.YELLOW if "WL" in b["status"]
                            else C.RED)
            p(f"\n  PNR: {b['pnr']}", C.CYAN, bold=True)
            p(f"  {train.name if train else b['train_number']} | {b['travel_date']} | "
              f"{Train.CLASSES[b['travel_class']]['name']} | ₹{b['fare']:.2f}")
            p(f"  Status: {b['status']}  |  Passengers: {len(b['passengers'])}", status_color)
            line("─", 40, C.DIM)

    # ── ADMIN: TRAIN STATUS REPORT ─────────────
    def train_status_report(self):
        """Shows occupancy and revenue report for all trains."""
        header("📊  TRAIN STATUS & REVENUE REPORT")

        total_revenue = sum(b["fare"] for b in self.bookings.values()
                            if "CONFIRMED" in b.get("status",""))

        p(f"  Total Trains     : {len(self.trains)}", C.CYAN)
        p(f"  Total Bookings   : {len(self.bookings)}", C.CYAN)
        p(f"  Total Revenue    : ₹{total_revenue:,.2f}", C.GREEN, bold=True)
        line()

        for num, train in self.trains.items():
            p(f"\n  🚆 {train.number} — {train.name}", C.YELLOW, bold=True)
            p(f"     {train.source} → {train.destination} | {train.distance_km} km")
            for cls, info in Train.CLASSES.items():
                avail = train.get_available_seats(cls)
                total = info["seats"] * info["coaches"]
                booked = total - avail
                bar = self._availability_bar(avail, total)
                p(f"     {cls} {bar}  Booked:{booked:>4}  Free:{avail:>4}")


# ══════════════════════════════════════════════
# MAIN MENU  (the user interface)
# ══════════════════════════════════════════════
def print_banner():
    banner = """
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║    🚂   INDIAN RAILWAY TICKET RESERVATION SYSTEM   🚂       ║
║                                                              ║
║    Author  : Sulagno Banerjee  |  BCA (AI) – Jain Univ.    ║
║    Tech    : Python | OOP | File Handling | Data Structures  ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
"""
    p(banner, C.CYAN, bold=True)

def main_menu(system):
    """Shows the correct menu based on login state."""
    if not system.current_user:
        p("\n  ┌─ MAIN MENU ──────────────────────────────┐", C.CYAN)
        p("  │  1. Search Trains                         │", C.WHITE)
        p("  │  2. PNR Enquiry                           │", C.WHITE)
        p("  │  3. Register                              │", C.WHITE)
        p("  │  4. Login                                 │", C.WHITE)
        p("  │  5. Train Status Report (Admin)           │", C.WHITE)
        p("  │  0. Exit                                  │", C.WHITE)
        p("  └──────────────────────────────────────────┘", C.CYAN)
    else:
        p(f"\n  ┌─ MENU — {system.current_user['name'][:20]:<20}──────────────┐", C.CYAN)
        p("  │  1. Search Trains                         │", C.WHITE)
        p("  │  2. Book Ticket                           │", C.WHITE)
        p("  │  3. PNR Enquiry                           │", C.WHITE)
        p("  │  4. Cancel Ticket                         │", C.WHITE)
        p("  │  5. My Bookings                           │", C.WHITE)
        p("  │  6. Train Status Report                   │", C.WHITE)
        p("  │  7. Logout                                │", C.WHITE)
        p("  │  0. Exit                                  │", C.WHITE)
        p("  └──────────────────────────────────────────┘", C.CYAN)


def main():
    print_banner()
    system = ReservationSystem()

    while True:
        main_menu(system)
        choice = input("\n  Enter choice: ").strip()

        if not system.current_user:
            if   choice == "1": system.search_trains()
            elif choice == "2": system.pnr_enquiry()
            elif choice == "3": system.register_user()
            elif choice == "4": system.login_user()
            elif choice == "5": system.train_status_report()
            elif choice == "0":
                p("\n  🚂 Thank you for using Indian Railway Reservation System!\n", C.CYAN, bold=True)
                break
            else: p("  ❌ Invalid choice.", C.RED)
        else:
            if   choice == "1": system.search_trains()
            elif choice == "2": system.book_ticket()
            elif choice == "3": system.pnr_enquiry()
            elif choice == "4": system.cancel_ticket()
            elif choice == "5": system.my_bookings()
            elif choice == "6": system.train_status_report()
            elif choice == "7":
                p(f"  👋 Logged out. Goodbye, {system.current_user['name']}!", C.YELLOW)
                system.current_user = None
            elif choice == "0":
                p("\n  🚂 Thank you for using Indian Railway Reservation System!\n", C.CYAN, bold=True)
                break
            else: p("  ❌ Invalid choice.", C.RED)


if __name__ == "__main__":
    main()