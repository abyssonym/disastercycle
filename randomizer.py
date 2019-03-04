from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses, get_random_degree,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch)
from randomtools.utils import (
    classproperty, cached_property, get_snes_palette_transformer,
    read_multi, write_multi, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)
from randomtools.itemrouter import ItemRouter, ItemRouterException
from collections import defaultdict
from os import path
from time import time, sleep, gmtime
from collections import Counter
from itertools import combinations
from sys import argv


VERSION = 1
KINSHIP_FILENAME = 'kinship.bin'
AI_PTR_FILENAME = 'enemy_ai_pointers.txt'
ESKILL_PTR_FILENAME = 'enemy_skill_pointers.txt'

nameslibrary = defaultdict(dict)
for nametype in ['demon', 'skill', 'race']:
    filename = '%s_names.txt' % nametype
    with open(path.join(tblpath, filename)) as f:
        for line in f:
            line = line.strip()
            index, name = line.split(' ', 1)
            index = int(index, 0x10)
            nameslibrary[nametype][index] = name

ai_pointers = {}
with open(path.join(tblpath, AI_PTR_FILENAME)) as f:
    for line in f:
        line = line.strip()
        pointer, line = line.split()
        assert line[0] == '#'
        length, filename = line.lstrip('#').split(',')
        pointer, length = int(pointer, 0x10), int(length, 0x10)
        name, extension = filename.split('.')
        assert extension == 'bf'
        assert name[:3] == 'ai_'
        name = name[3:].upper()
        assert name not in ai_pointers
        assert pointer not in ai_pointers
        ai_pointers[name] = (pointer, length)
        ai_pointers[pointer] = name

eskill_pointers = {}
with open(path.join(tblpath, ESKILL_PTR_FILENAME)) as f:
    for line in f:
        line = line.strip()
        pointer, line = line.split()
        assert line[0] == '#'
        filename = line.lstrip('#')
        pointer = int(pointer, 0x10)
        name, extension = filename.split('.')
        assert extension == 'bin'
        assert name[:3] == 'sk_'
        name = name[3:].upper()
        assert name not in eskill_pointers
        assert pointer not in eskill_pointers
        eskill_pointers[name] = pointer
        eskill_pointers[pointer] = name


ALLY_TARGET_SKILLS = set(range(0x65, 0x94)) - set(range(0x7E, 0x83))
ALLY_TARGET_SKILLS |= {0xF8}

def get_similar_skill(skill, candidates):
    if skill >= 0x15f:
        # passive skill for some reason??
        return skill
    candidates = [c for c in candidates if c < 0x15f]

    if skill > 0xC0 and skill not in ALLY_TARGET_SKILLS and skill != 0x152:
        raise Exception('Unexpected skill.')

    if skill in ALLY_TARGET_SKILLS:
        candidates = sorted(set(candidates) & ALLY_TARGET_SKILLS)
    else:
        candidates = sorted(set(candidates) - ALLY_TARGET_SKILLS)

    if candidates:
        chosen = random.choice(candidates)
        #print nameslibrary['skill'][skill], '->',
        #print nameslibrary['skill'][chosen]
        assert 'Dummy' not in nameslibrary['skill'][chosen]
        return chosen
    else:
        return skill


class NakamaParent(TableObject):
    def __repr__(self):
        stats = [self.make_display_line(attr) for attr in self.STATS]
        elements = [self.make_display_line(attr) for attr in self.ELEMENTS]
        ailments = [self.make_display_line(attr) for attr in self.AILMENTS]
        rewards = [self.make_display_line(attr) for attr in self.REWARDS]
        assert len(ailments) == 10
        table = self.make_display_table(
            stats, elements, ailments[:5], ailments[5:], rewards)
        s = '{0:0>3X} {1:0>3X} {2} {3}\n'.format(
            self.index, self.nakama_index,
            self.race_name, self.name.strip('\x00'))
        s += table + '\n'
        s += 'SKILLS:\n'
        table = self.make_display_table(self.all_skills_names[0::3],
                                        self.all_skills_names[1::3],
                                        self.all_skills_names[2::3])
        s += table + '\n'
        return s.strip()

    @cached_property
    def rank(self):
        return self.old_data['lv']

    @cached_property
    def nakama(self):
        return NakamaObject.get(self.index)

    @cached_property
    def enemy(self):
        return EnemyObject.get(self.index)

    @cached_property
    def race_name(self):
        return nameslibrary['race'][self.nakama.race]

    @cached_property
    def dsource(self):
        return DSourceObject.get_by_dsource_index(
            self.nakama.old_data['dsource_index'])

    @cached_property
    def dsource_skills(self):
        if self.dsource is None:
            return []
        return self.dsource.old_data['skills']

    @cached_property
    def all_skills(self):
        skills = self.nakama.old_data['skills'] + self.dsource_skills
        if self.eskills is not None:
            skills += self.eskills.old_data['skills']
        return sorted(set([s for s in skills if s]))

    @property
    def all_skills_names(self):
        return [nameslibrary['skill'][s] for s in self.all_skills]

    @cached_property
    def is_compendium_demon(self):
        return any(self.dsource_skills)

    @cached_property
    def kinship_rankings(self):
        sorted_nakama = sorted(NakamaObject.every,
                               key=lambda n: self.get_kinship(n),
                               reverse=True)
        sorted_nakama = [n for n in sorted_nakama if n.intershuffle_valid]
        if self is self.canonical_version:
            sorted_nakama = [n for n in sorted_nakama
                             if n is n.canonical_version]
        elif self.is_compendium_demon:
            sorted_nakama = [n for n in sorted_nakama if n.is_compendium_demon]
        return sorted_nakama

    @classmethod
    def get_attr_minmax(cls, attr):
        if not hasattr(cls, '_attr_minmax_cache'):
            cls._attr_minmax_cache = {}
        if attr in cls._attr_minmax_cache:
            return cls._attr_minmax_cache[attr]

        values = [o.old_data[attr] for o in cls.every]
        cls._attr_minmax_cache[attr] = (min(values), max(values))
        return cls.get_attr_minmax(attr)

    def get_resistance_flag(self, res, old=False):
        if old:
            val = self.old_data['res_%s_val' % res]
        else:
            val = getattr(self, 'res_%s_val' % res)
        flag = val >> 9
        flag = {0b0000: '',
                0b0010: 'N',
                0b0100: 'W',
                0b0110: 'R',
                0b1000: 'D',
                0b1010: 'S',
                0b110010: '?',
               }[flag]
        return flag

    def get_effective_resistance_value(self, res, old=False):
        if old:
            val = self.old_data['res_%s_val' % res]
        else:
            val = getattr(self, 'res_%s_val' % res)
        val = val & 0x1FF
        flag = self.get_resistance_flag(res, old=old)
        if flag and flag in 'NRD?':
            val = 0
        elif flag == 'W' and val == 100:
            val = 101
        return val

    def make_display_table(self, *columns):
        columns = [c for c in columns if c]
        if not columns:
            return ''
        widest = max([len(line) for column in columns for line in column])
        tallest = max([len(column) for column in columns])

        for column in columns:
            while len(column) < tallest:
                column.append('')

        assert len(set(len(column) for column in columns)) == 1
        s = ''
        for row in zip(*columns):
            line = ' | '.join(('{0:%s}' % widest).format(r) for r in row)
            s += line.rstrip() + '\n'
        return s.rstrip()

    def make_display_line(self, attr):
        if attr in self.ELEMENTS + self.AILMENTS:
            val = self.get_effective_resistance_value(attr)
            flag = self.get_resistance_flag(attr)
            return '{0: <3} {1: >3}{2: >1}'.format(attr.upper(), val, flag)
        else:
            assert attr in self.STATS + self.REWARDS
            return '{0: <2} {1: >5}'.format(
                attr.upper(), getattr(self, attr))

    def _get_kinship_core(self, other):
        assert self.index <= other.index
        if hasattr(NakamaObject, '_kinship_loaded'):
            key = (self.index, other.index)
            if key in NakamaObject._kinship_loaded:
                return NakamaObject._kinship_loaded[key]

        features, weights = [], []

        features.append(
            1 if self.old_data['race'] == other.old_data['race'] else 0)
        weights.append(0.25)
        for attr in ['alignment_ld', 'alignment_lc']:
            a, b = self.old_data[attr], other.old_data[attr]
            if a == b:
                features.append(1)
            elif 1 in [a, b]:
                features.append(0.5)
            else:
                features.append(0)
            weights.append(0.5)

        attrs = self.STATS + ['st_growth', 'vi_growth', 'ag_growth',
                              'lu_growth', 'ma_growth']
        assert 'lv' in attrs
        for attr in attrs:
            a, b = self.old_data[attr], other.old_data[attr]
            low, high = self.get_attr_minmax(attr)
            maxdiff = float(abs(high - low))
            mydiff = abs(a - b)
            features.append(1-(mydiff / maxdiff))
            if attr == 'lv':
                weights.append(1)
            else:
                weights.append(1.0 / (len(attrs)-1))

        rescode_dict = {
                'D': 0.0,
                'R': 0.0,
                'N': 0.1,
                'S': 0.45,
                '':  0.65,
                'W': 1.0,
                }
        for reses in [self.ELEMENTS, self.AILMENTS]:
            for res in reses:
                a = self.get_effective_resistance_value(res, old=True)
                b = other.get_effective_resistance_value(res, old=True)
                maxdiff = 300.0
                mydiff = abs(a - b)
                assert mydiff <= maxdiff
                features.append(1-(mydiff / maxdiff))
                weights.append(1.0 / len(reses))

                if reses is self.ELEMENTS:
                    a = self.get_resistance_flag(res, old=True)
                    b = other.get_resistance_flag(res, old=True)
                    a = rescode_dict[a]
                    b = rescode_dict[b]
                    diff = abs(a-b)
                    features.append(1-diff)
                    weights.append(1.0 / len(reses))

        for i in xrange(16):
            a = self.old_data['inheritance'] & (1 << i)
            b = other.old_data['inheritance'] & (1 << i)
            features.append(1 if a == b else 0)
            weights.append(2.0 / 16.0)

        assert len(weights) == len(features)
        wavg = sum(weights) / len(weights)
        wfs = [(w*f/wavg) for (w, f) in zip(weights, features)]

        distance = sum([wf**2 for wf in wfs]) ** 0.5
        distance = int(round(distance * (10**8)))
        assert distance < (2**32)
        return distance

    def get_kinship(self, other):
        if not hasattr(NakamaObject, '_kinship_loaded'):
            self.load_kinship(KINSHIP_FILENAME)

        if self.index > other.index:
            return other.get_kinship(self)
        if self is not self.nakama:
            return self.nakama.get_kinship(other.nakama)
        if not hasattr(self, '_kinship_cache'):
            self._kinship_cache = {}
        if other.index in self._kinship_cache:
            return self._kinship_cache[other.index]
        assert type(self) is type(other)

        distance = self._get_kinship_core(other)

        if other is not self:
            max_distance = self.get_kinship(self)
            assert max_distance >= distance
            distance = mutate_normal(distance, minimum=0, maximum=max_distance,
                                     random_degree=self.random_degree ** 2,
                                     return_float=True, wide=True)

        self._kinship_cache[other.index] = distance
        return self.get_kinship(other)

    @classmethod
    def save_kinship(cls, filename):
        f = open(path.join(tblpath, filename), 'w+')
        f.close()
        f = open(path.join(tblpath, filename), 'r+b')
        for n1 in NakamaObject.every:
            for n2 in NakamaObject.every:
                if n1.index > n2.index:
                    continue
                kinship = n1._get_kinship_core(n2)
                write_multi(f, n1.index, length=2)
                write_multi(f, n2.index, length=2)
                write_multi(f, kinship, length=4)
        f.close()
        NakamaObject.load_kinship(filename)

    @classmethod
    def load_kinship(cls, filename):
        if not hasattr(NakamaObject, '_kinship_loaded'):
            NakamaObject._kinship_loaded = {}

        try:
            f = open(path.join(tblpath, filename), 'r+b')
        except IOError:
            print 'Generating kinship from scratch. This may take some time...'
            return

        while True:
            pointer = f.tell()
            peek = f.read(8)
            if len(peek) < 8:
                break
            f.seek(pointer)
            index1 = read_multi(f, length=2)
            index2 = read_multi(f, length=2)
            assert index1 <= index2
            kinship = read_multi(f, length=4)
            NakamaObject._kinship_loaded[(index1, index2)] = kinship
        f.close()

    def get_similar_by_kinship(self):
        if not self.intershuffle_valid:
            return self
        candidates = self.kinship_rankings
        index = candidates.index(self)
        index = mutate_normal(index, minimum=0, maximum=len(candidates)-1,
                              random_degree=self.random_degree ** 2, wide=True)
        return candidates[index]

    def get_similar(self, *args, **kwargs):
        return self.get_similar_by_kinship()


class NakamaObject(NakamaParent):
    STATS = ['lv', 'st', 'ma', 'vi', 'ag', 'lu']
    REWARDS = []
    ELEMENTS = ['phy', 'gun', 'fir', 'ice', 'ele', 'win', 'exp', 'cur', 'alm']
    AILMENTS = ['sto', 'rag', 'par', 'bom', 'str',
                'poi', 'cha', 'mut', 'fea', 'sle']

    randomselect_attributes = [
        'race', 'alignment_ld', 'alignment_lc', 'inheritance',
        ('st', 'st_growth'), ('vi', 'vi_growth'), ('ag', 'ag_growth'),
        ('lu', 'lu_growth'), ('ma', 'ma_growth'),
        #('hits_misc', 'hits_count'),
        'attack_element', ('attack_ailment', 'ailment_chance'),
        'res_phy_val', 'res_gun_val', 'res_exp_val', 'res_cur_val',
        'res_fir_val', 'res_ice_val', 'res_ele_val', 'res_win_val',
        'res_sle_val', 'res_poi_val', 'res_par_val', 'res_cha_val',
        'res_mut_val', 'res_sto_val', 'res_fea_val', 'res_str_val',
        'res_bom_val', 'res_rag_val', 'res_alm_val',
        ]
    mutate_attributes = {
        'lv': None, 'st': None, 'ma': None, 'vi': None, 'ag': None, 'lu': None,
        'st_growth': None, 'vi_growth': None, 'ag_growth': None,
        'lu_growth': None, 'ma_growth': None,
        }

    @cached_property
    def name(self):
        return nameslibrary['demon'][self.index]

    @cached_property
    def intershuffle_valid(self):
        if (self.name.lower() in ['dummy', 'unknown']
                or len(set(self.name)) == 1):
            return False
        if self.old_data['lv'] != self.enemy.old_data['lv']:
            return False
        return True

    @cached_property
    def is_big_boss(self):
        return self is self.canonical_version and not self.is_compendium_demon

    @cached_property
    def sprite(self):
        return self.enemy.sprite

    @cached_property
    def companion_group(self):
        return [n for n in NakamaObject.every if self.name == n.name
                and self.old_data['race'] == n.old_data['race']]

    @cached_property
    def canonical_version(self):
        candidates = self.companion_group
        temp = [c for c in candidates if c.dsource is not None]
        if temp:
            candidates = temp
        temp = [c for c in candidates if c.is_compendium_demon]
        if temp:
            candidates = temp
        return min(candidates, key=lambda n: n.index)

    @cached_property
    def named_enemy(self):
        candidates = [n.enemy for n in self.companion_group if
                      len(n.enemy.name.rstrip('\x00')) >= 2]
        if not candidates:
            return None
        elif len(candidates) == 1:
            return candidates[0]
        elif self.enemy in candidates:
            return self.enemy
        elif self.canonical_version.enemy in candidates:
            return self.canonical_version.enemy
        return min(candidates,
            key=lambda c: (abs(self.old_data['lv']-c.old_data['lv']), c.index))

    @cached_property
    def eskills(self):
        enemy = self.named_enemy
        if enemy:
            return enemy.eskills
        return None

    @classproperty
    def valid_skills(cls):
        if hasattr(NakamaObject, '_valid_skills'):
            return NakamaObject._valid_skills

        valid_skills = set([])
        for n in NakamaObject.every:
            if n.is_compendium_demon:
                valid_skills |= set(n.old_data['skills'])
                valid_skills |= set(n.dsource_skills)
        valid_skills.remove(0)
        NakamaObject._valid_skills = valid_skills

        return NakamaObject.valid_skills

    def randomize_skills(self):
        old_num = len([s for s in self.old_data['skills'] if s])
        num_skills = 0
        while old_num and num_skills <= 0:
            num_skills = len([s for s in
                              self.get_similar().old_data['skills'] if s])
        new_skills = set([])
        while len(new_skills) < num_skills:
            chosen = self.get_similar()
            candidates = [s for s in
                          chosen.old_data['skills'] + chosen.all_skills if s]
            if self.is_compendium_demon:
                candidates = [s for s in candidates
                              if s in NakamaObject.valid_skills]
            if candidates:
                chosen = random.choice(sorted(candidates))
                new_skills.add(chosen)

        new_skills = sorted(new_skills)
        self.skills = ([0]*6)
        self.skills[:len(new_skills)] = new_skills

        if self.dsource is None:
            return

        old_num = len([s for s in self.dsource_skills if s])
        num_skills = 0
        while old_num and num_skills <= 0:
            num_skills = len([s for s in
                              self.get_similar().dsource_skills if s])
        new_dskills = set([])
        while len(new_dskills) < num_skills:
            chosen = self.get_similar()
            candidates = new_skills + [s for s in chosen.all_skills if s]
            if self.is_compendium_demon:
                candidates = [s for s in candidates
                              if s in NakamaObject.valid_skills]
            if candidates:
                chosen = random.choice(sorted(candidates))
                new_dskills.add(chosen)

        new_dskills = sorted(new_dskills)
        self.dsource.skills = ([0]*3)
        self.dsource.skills[:len(new_dskills)] = new_dskills

    def randomize(self):
        self.randomize_skills()
        super(NakamaObject, self).randomize()

    @classmethod
    def full_preclean(cls):
        races = sorted(set(n.race for n in NakamaObject))
        for r in races:
            nakamas = [n for n in NakamaObject.ranked
                       if n.is_compendium_demon and n.race == r]
            while True:
                nakamas = sorted(
                    nakamas, key=lambda n: n.lv)
                for n1, n2 in zip(nakamas, nakamas[1:]):
                    n1.lv = max(1, min(99, n1.lv))
                    n2.lv = max(1, min(99, n2.lv))
                    assert n2.lv >= n1.lv
                    if n1.lv == n2.lv == 99:
                        n1.lv = mutate_normal(
                            98, 1, maximum=98,
                            random_degree=n1.random_degree**2, wide=True)
                        break
                    if n1.lv == n2.lv:
                        n2.lv = mutate_normal(
                            n2.lv+1, minimum=n2.lv+1, maximum=99,
                            random_degree=n2.random_degree**2, wide=True)
                        break
                else:
                    break
        super(NakamaObject, cls).full_preclean()

    def preclean_stats(self):
        canon = self.canonical_version
        if self is canon and not self.is_big_boss:
            return

        for attr in self.old_data:
            if attr.startswith('res_'):
                _, res, _ = attr.split('_')
                oldval = self.get_effective_resistance_value(res, old=True)
                canonval = canon.get_effective_resistance_value(res)
                newval = self.get_effective_resistance_value(res)
                if (newval > oldval and canonval > oldval and oldval < 50 and
                        res in ['exp', 'cur', 'sto', 'rag', 'bom', 'sle']):
                    setattr(self, attr, self.old_data[attr])
                elif (oldval < canonval and oldval < 50
                        and res in self.AILMENTS):
                    setattr(self, attr, self.old_data[attr])
                elif canonval <= newval or res in [
                        'phy', 'gun', 'alm', 'fir', 'ice', 'ele', 'win']:
                    setattr(self, attr, getattr(canon, attr))

                newval = self.get_effective_resistance_value(res)
                if (self.is_big_boss and oldval < newval
                        and random.choice([True, False])):
                    setattr(self, attr, self.old_data[attr])
            elif attr in self.STATS:
                old_a, old_b = (self.old_data[attr],
                                self.canonical_version.old_data[attr])
                new_b = getattr(self.canonical_version, attr)

                new_a = old_a * (new_b / float(old_b))
                low, high = self.get_attr_minmax(attr)
                new_a = int(round(max(low, min(high, new_a))))
                setattr(self, attr, new_a)

                if (self.is_big_boss and new_a < old_a
                        and random.choice([True, False])):
                    setattr(self, attr, old_a)
            elif (self.old_data[attr] == canon.old_data[attr]):
                setattr(self, attr, getattr(canon, attr))

    def preclean_skills(self):
        canon = self.canonical_version
        if self is canon:
            return

        if set(self.old_data['skills']) <= set(canon.old_data['skills'] + [0]):
            self.skills = list(canon.skills)
            return
        elif set(canon.old_data['skills']) == {0}:
            if any(canon.skills):
                self.skills = list(canon.skills)
            return

        raise Exception('Unable to make skills match.')

    def preclean(self):
        self.preclean_stats()
        self.preclean_skills()

    def cleanup(self):
        assert hasattr(EnemyObject, 'precleaned') and EnemyObject.precleaned
        for attr in self.old_data:
            if attr.startswith('res_') and getattr(self, attr) == 0:
                setattr(self, attr, 0x400)

        if AllyObject.flag not in get_flags():
            for attrs in (self.randomselect_attributes +
                          sorted(self.mutate_attributes)):
                if isinstance(attrs, basestring):
                    attrs = [attrs]
                for attr in attrs:
                    if attr not in RaceObject.attributes + ['skills']:
                        setattr(self, attr, self.old_data[attr])

        if RaceObject.flag not in get_flags():
            for attr in RaceObject.attributes:
                setattr(self, attr, self.old_data[attr])

        if DSourceObject.flag not in get_flags():
            self.skills = self.old_data['skills']
            if self.dsource:
                self.dsource.skills = self.dsource.old_data['skills']


class AllyObject(TableObject):
    flag = 'n'
    flag_description = 'nakama (demon allies)'


class EnemyObject(NakamaParent):
    flag = 'e'
    flag_description = 'enemy stats'

    STATS = ['lv', 'hp', 'mp', 'st', 'ma', 'vi', 'ag', 'lu']
    REWARDS = ['xp', 'mac']
    ELEMENTS = ['phy', 'gun', 'fir', 'ice', 'ele', 'win', 'exp', 'cur', 'alm']
    AILMENTS = ['sto', 'rag', 'par', 'bom', 'str',
                'poi', 'cha', 'mut', 'fea', 'sle']

    mutate_attributes = {
        'xp': None, 'mac': None,
        }

    @classproperty
    def after_order(cls):
        return [NakamaObject]

    @cached_property
    def eskills(self):
        name = self.name.rstrip('\x00')
        return EnemySkillObject.get_by_name(name)

    def update_ai(self):
        name = self.name.rstrip('\x00')
        if len(name) < 2:
            return
        ai_pointer, ai_length = ai_pointers[name.upper()]
        old_skills = set(self.nakama.all_skills)
        new_skills = set(self.nakama.skills)
        if self.nakama.canonical_version.dsource is not None:
            new_skills |= set(self.nakama.canonical_version.dsource.skills)
        new_skills -= {0}

        ai_skills = set([])
        offset = 0
        f = open(get_outfile(), 'r+b')
        while offset < ai_length:
            f.seek(ai_pointer + offset)
            ai_code = read_multi(f, length=2)
            f.seek(ai_pointer + offset + 2)
            value = read_multi(f, length=2)
            if ai_code == 0x1d and value and value in new_skills:
                ai_skills.add(value)
            elif (ai_code == 0x1d and value
                    and value in old_skills and value not in new_skills):
                new_value = get_similar_skill(value, new_skills)
                ai_skills.add(new_value)
                f.seek(ai_pointer + offset + 2)
                write_multi(f, new_value, length=2)
            offset += 4
        f.close()

        if self.nakama.canonical_version.dsource is not None:
            dsource_skills = self.nakama.canonical_version.dsource.skills
        else:
            dsource_skills = []
        eskill_candidates = []
        eskill_leftovers = []
        for skills in [(ai_skills & new_skills) - old_skills,
                       self.nakama.skills, dsource_skills]:
            skills = sorted(set(skills))
            leftovers = [s for s in skills if s >= 0x15f]
            skills = [s for s in skills if s not in leftovers]
            random.shuffle(skills)
            for s in skills:
                if s not in eskill_candidates:
                    eskill_candidates.append(s)
            random.shuffle(leftovers)
            for s in leftovers:
                if s not in eskill_leftovers:
                    eskill_leftovers.append(s)
        eskill_candidates += leftovers
        eskill_candidates = sorted(eskill_candidates[:6])
        while len(eskill_candidates) < 8:
            eskill_candidates.append(0)
        assert self.eskills is not None
        self.eskills.skills = eskill_candidates

    def preclean(self):
        assert not hasattr(NakamaObject, 'cleaned')
        for attrs in NakamaObject.randomselect_attributes + ['hp', 'mp']:
            if isinstance(attrs, basestring):
                attrs = [attrs]
            for attr in attrs:
                if not hasattr(self, attr):
                    continue

                if hasattr(self.nakama, attr):
                    nattr = attr
                else:
                    nattr = {'hp': 'vi',
                             'mp': 'ma',
                             }[attr]

                old_a, old_b = (self.old_data[attr],
                                self.nakama.old_data[nattr])
                new_b = getattr(self.nakama, nattr)
                if attr.startswith('res_'):
                    setattr(self, attr, new_b)
                elif attr in self.STATS:
                    new_a = old_a * (new_b / float(old_b))
                    low, high = self.get_attr_minmax(attr)
                    new_a = int(round(max(low, min(high, new_a))))
                    setattr(self, attr, new_a)
                elif old_a == old_b and attr == nattr:
                    setattr(self, attr, new_b)

        # nerf early zone enemies
        if self.old_data['lv'] < 10:
            for attr in self.STATS:
                old, new = self.old_data[attr], getattr(self, attr)
                if new > old:
                    if self.old_data['lv'] == 1:
                        ratio = 0
                    else:
                        ratio = (self.old_data['lv'] / 10.0) ** 2
                    balanced = (new*ratio) + (old*(1-ratio))
                    assert old <= balanced <= new
                    setattr(self, attr, int(round(balanced)))

        if (EnemyObject.flag in get_flags()
                and EnemySkillObject.flag in get_flags()):
            self.update_ai()

    def cleanup(self):
        if EnemyObject.flag not in get_flags():
            for attr in self.STATS:
                setattr(self, attr, self.old_data[attr])

        for attr in self.old_data:
            if attr.startswith('res_') and getattr(self, attr) == 0:
                setattr(self, attr, 0x400)

        if 'easymodo' in get_activated_codes():
            for stat in self.STATS:
                setattr(self, stat, 1)
            self.mp = 9999
            self.hp = self.old_data['hp']

        if self.index == 0x1a2:
            assert self.nakama.name == 'Gore'
            for stat in self.STATS:
                setattr(self, stat, 99)
            self.hp = 9999


class EnemySkillObject(TableObject):
    flag = 's'
    flag_description = 'demon skills'

    def __repr__(self):
        s = '{0:0>3X} {1}\n'.format(self.index, self.name)
        for sk in self.skills:
            if sk:
                s += '{0}\n'.format(nameslibrary['skill'][sk])
        return s.strip()

    @cached_property
    def name(self):
        return eskill_pointers[self.pointer]

    @cached_property
    def enemy(self):
        candidates = [e for e in EnemyObject.every if e.eskill is self]
        assert len(candidates) == 1
        return candidates[0]

    @classmethod
    def get_by_name(cls, name):
        if name in eskill_pointers:
            return EnemySkillObject.get_by_pointer(
                eskill_pointers[name.upper()])
        return None

    def cleanup(self):
        self.num_skills = len([s for s in self.skills if s])


class DSourceObject(TableObject):
    flag = 's'

    @classmethod
    def get_by_dsource_index(cls, index):
        candidates = [d for d in DSourceObject.every
                      if d.dsource_index == index]
        if len(candidates) == 0:
            return None
        assert len(candidates) == 1
        return candidates[0]


class RaceObject(TableObject):
    flag = 'f'
    flag_description = 'demon races (fusion recipes) and alignments'
    attributes = ['race', 'alignment_ld', 'alignment_lc']


if __name__ == '__main__':
    try:
        print ('You are using the Shin Megami Tensei: Strange Journey '
               'randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {'easymodo': ['easymodo'],
                }

        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True)

        #NakamaObject.save_kinship('kinship.bin')

        clean_and_write(ALL_OBJECTS)

        pixie = NakamaObject.get(0x92)
        nakamas = pixie.kinship_rankings

        #for n in nakamas:
        #    if n.intershuffle_valid:
        #        print n
        #        print '-' * 79

        finish_interface()

    except Exception, e:
        print 'ERROR: %s' % e
        raw_input('Press Enter to close this program. ')
