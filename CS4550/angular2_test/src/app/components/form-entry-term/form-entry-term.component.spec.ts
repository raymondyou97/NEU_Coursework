import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { FormEntryTermComponent } from './form-entry-term.component';

describe('FormEntryTermComponent', () => {
  let component: FormEntryTermComponent;
  let fixture: ComponentFixture<FormEntryTermComponent>;

  beforeEach(async(() => {
    TestBed.configureTestingModule({
      declarations: [ FormEntryTermComponent ]
    })
    .compileComponents();
  }));

  beforeEach(() => {
    fixture = TestBed.createComponent(FormEntryTermComponent);
    component = fixture.componentInstance;
    fixture.detectChanges();
  });

  it('should create', () => {
    expect(component).toBeTruthy();
  });
});
