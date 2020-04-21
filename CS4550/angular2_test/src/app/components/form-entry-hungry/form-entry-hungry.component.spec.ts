import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { FormEntryHungryComponent } from './form-entry-hungry.component';

describe('FormEntryHungryComponent', () => {
  let component: FormEntryHungryComponent;
  let fixture: ComponentFixture<FormEntryHungryComponent>;

  beforeEach(async(() => {
    TestBed.configureTestingModule({
      declarations: [ FormEntryHungryComponent ]
    })
    .compileComponents();
  }));

  beforeEach(() => {
    fixture = TestBed.createComponent(FormEntryHungryComponent);
    component = fixture.componentInstance;
    fixture.detectChanges();
  });

  it('should create', () => {
    expect(component).toBeTruthy();
  });
});
